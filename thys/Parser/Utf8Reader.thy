theory Utf8Reader
  imports
    Main HOL.Bit_Operations "HOL-Library.Word"
    Refine_Monadic.Refine_Monadic
    "HOL-Library.Monad_Syntax"
    Refine_Imperative_HOL.IICF 
    "HOL-Library.Code_Target_Nat"
    Native_Word.Native_Cast_Uint
begin

(*commit_ignore_start*)
sledgehammer_params[provers="cvc4 cvc5 verit z3 e iprover leo2 leo3 satallax spass vampire zipperposition"]
(*commit_ignore_end*)

text \<open>
  UTF-8 is a special encoding for Unicode characters which can be simplified as:
  \begin{center}
    \begin{tabular}{cccccc}
      \toprule
      Lower bound & Upper bound & \multicolumn{4}{c}{Pattern (bits)} \\ 
      \midrule
      \verb|0x000000| & \verb|0x00007F| & \verb|0xxxxxxx| \\
      \verb|0x000080| & \verb|0x0007FF| & \verb|110xxxxx 10xxxxxx| \\
      \verb|0x000800| & \verb|0x00FFFF| & \verb|1110xxxx 10xxxxxx 10xxxxxx| \\
      \verb|0x010000| & \verb|0x10FFFF| & \verb|11110xxx 10xxxxxx 10xxxxxx 10xxxxxx| \\
      \bottomrule 
    \end{tabular}
  \end{center}
  In the pattern column, ``x'' marks a data bit.
  To obtain the final UTF-8 encoded codepoint, we simply ``glue'' those ``x'' bits together.
  However, we must be cautious in doing so: for example, if we take the sequence
  \verb|11000000 10000001|, the associated codepoint is \verb|00000 000001|, which is the same
  codepoint as the sequence \verb|00000001|.
  To remedy this, the codepoint associated to the second row must be strictly bigger than \verb|0x7F|.
  Similarly, the codepoint associated to the third row must be strictly bigger than \verb|0x7FF|, and
  the codepoint associated to the fourth row must be strictly bigger than \verb|0xFFFF|.
\<close>

section \<open>Byte strings\<close>

text \<open>
  We need to define a type for unsigned 8-bit integers, which we'll simply define as an @{typ int}.
  This type will allow us to define our input string (which we'll define as a list of unsigned
  8-bit integers).
  Because it's much better, we'll also setup the code generator to use the host language types if
  possible (e.g. \<open>Word8\<close> in Haskell).
\<close>

type_synonym byte_string = \<open>uint8 list\<close>

text \<open>
  We will later refine the @{typ byte_string} to remove the list and get an efficient string
  representation.
\<close> 

section \<open>Unicode codepoint strings\<close>

text \<open>
  UTF-8 codepoints can all be stored within an unsigned 24-bits integers (count the number of ``x''s
  in the last row of the table at the beginning: 21 if you're lazy).
  It is better to simply round this to the next multiple of 8 (@{term \<open>24 = 3 * 8\<close>}). 

  We will setup the code generator to use unsigned 32-bits integers if unsigned 24-bits integers are
  not easily available in the target language.
\<close> 

type_synonym codepoint_string = \<open>uint32 list\<close>

text \<open>
  We will also refine the @{typ codepoint_string} type to get rid of the list and get an memory- and
  CPU-efficient implementation. 
\<close>

(* This is safe because @{typ word32} is bigger than @{typ word8}. *)
definition word8_to_word24 :: \<open>uint8 \<Rightarrow> uint32\<close> where
  \<open>word8_to_word24 w \<equiv> uint32_of_uint (uint_of_uint8 w)\<close> 

section \<open>UTF-8 validity\<close>

text \<open>
  A @{typ uint8} corresponds to an ASCII character if its most significant bit is set to \<open>0\<close>.
\<close> 

abbreviation is_one_byte :: \<open>uint8 \<Rightarrow> bool\<close> where
  \<open>is_one_byte w \<equiv> \<not> bit w 7\<close> 

text \<open>
  A continuation byte is a byte of the form \verb|10xxxxxx|.
\<close> 

definition is_continuation_byte :: \<open>uint8 \<Rightarrow> bool\<close> where
  \<open>is_continuation_byte w \<equiv> bit w 7 \<and> \<not> bit w 6\<close> 

lemma is_not_one_if_cont: \<open>is_continuation_byte w \<Longrightarrow> \<not> is_one_byte w\<close>
  unfolding is_continuation_byte_def
  by blast 

lemma is_not_cont_if_one: \<open>is_one_byte w \<Longrightarrow> \<not> is_continuation_byte w\<close>
  unfolding is_continuation_byte_def
  by blast 

lemma is_cont_iff_not_one [iff]: \<open>\<not> bit w 6 \<Longrightarrow> \<not> is_one_byte w \<longleftrightarrow> is_continuation_byte w\<close>
  unfolding is_continuation_byte_def
  by blast 

definition cont_data_bits :: \<open>uint8 \<Rightarrow> uint32\<close> where
  \<open>cont_data_bits \<equiv> word8_to_word24 \<circ> take_bit 6\<close> 

text \<open>
  A two byte sequence is valid if:
  \<^item> the first byte starts with ▩\<open>110\<close>;
  \<^item> the second bytes starts with \<^verbatim>\<open>10\<close>;
  \<^item> the integer number obtained from concatenating the remaining bits is strictly bigger than \<open>0x7F\<close>.
\<close> 

definition two_byte_codepoint :: \<open>uint8 \<Rightarrow> uint8 \<Rightarrow> uint32\<close> where
  \<open>two_byte_codepoint w1 w2 \<equiv> and (push_bit 6 (word8_to_word24 (take_bit 5 w1))) (cont_data_bits w2)\<close> 

abbreviation is_two_bytes :: \<open>uint8 \<Rightarrow> uint8 \<Rightarrow> bool\<close> where
  \<open>is_two_bytes w1 w2 \<equiv> bit w1 7 \<and> bit w1 6 \<and> \<not> bit w1 5 \<and> is_continuation_byte w2 \<and>
    two_byte_codepoint w1 w2 > 0x7F\<close>

text \<open>

\<close>

definition three_byte_codepoint :: \<open>uint8 \<Rightarrow> uint8 \<Rightarrow> uint8 \<Rightarrow> uint32\<close> where
  \<open>three_byte_codepoint w1 w2 w3 \<equiv>
    and (push_bit 6 (and (push_bit 6 (word8_to_word24 (take_bit 4 w1))) (cont_data_bits w2)))
      (cont_data_bits w3)\<close> 

abbreviation is_three_bytes :: \<open>uint8 \<Rightarrow> uint8 \<Rightarrow> uint8 \<Rightarrow> bool\<close> where
  \<open>is_three_bytes w1 w2 w3 \<equiv> bit w1 7 \<and> bit w1 6 \<and> bit w1 5 \<and> \<not> bit w1 4 \<and>
    is_continuation_byte w2 \<and> is_continuation_byte w3 \<and>
    three_byte_codepoint w1 w2 w3 > 0x7FF\<close> 

text \<open>

\<close>

definition four_byte_codepoint :: \<open>uint8 \<Rightarrow> uint8 \<Rightarrow> uint8 \<Rightarrow> uint8 \<Rightarrow> uint32\<close> where
  \<open>four_byte_codepoint w1 w2 w3 w4 \<equiv>
    and (push_bit 6 (and (push_bit 6 (and (push_bit 6 (word8_to_word24 (take_bit 3 w1)))
      (cont_data_bits w2))) (cont_data_bits w3))) (cont_data_bits w4)\<close> 

abbreviation is_four_bytes :: \<open>uint8 \<Rightarrow> uint8 \<Rightarrow> uint8 \<Rightarrow> uint8 \<Rightarrow> bool\<close> where
  \<open>is_four_bytes w1 w2 w3 w4 \<equiv> bit w1 7 \<and> bit w1 6 \<and> bit w1 5 \<and> bit w1 4 \<and> \<not> bit w1 3 \<and>
    is_continuation_byte w2 \<and> is_continuation_byte w3 \<and> is_continuation_byte w4 \<and>
    four_byte_codepoint w1 w2 w3 w4 > 0xFFFF\<close> 

text \<open>
  Given an input byte string, we want to determine whether it represents a valid UTF-8 encoded string
  or not.

  A byte string is UTF-8-valid if it follows the table at the beginning, along with the additional
  restrictions that the deciphered codepoints do not going outside of their expected bounds.
\<close> 

inductive utf8_valid :: \<open>byte_string \<Rightarrow> bool\<close> where
  utf8_valid_empty: \<open>utf8_valid []\<close>
| utf8_valid_one_byte: \<open>is_one_byte w \<Longrightarrow> utf8_valid ws \<Longrightarrow> utf8_valid (w # ws)\<close>
| utf8_valid_two_bytes: \<open>is_two_bytes w1 w2 \<Longrightarrow> utf8_valid ws \<Longrightarrow> utf8_valid (w1 # w2 # ws)\<close> 
| utf8_valid_three_bytes:
  \<open>is_three_bytes w1 w2 w3 \<Longrightarrow> utf8_valid ws \<Longrightarrow> utf8_valid (w1 # w2 # w3 # ws)\<close>
| utf8_valid_four_bytes:
  \<open>is_four_bytes w1 w2 w3 w4 \<Longrightarrow> utf8_valid ws \<Longrightarrow> utf8_valid (w1 # w2 # w3 # w4 # ws)\<close> 

lemma utf8_valid_one_byte_snoc: \<open>is_one_byte w \<Longrightarrow> utf8_valid ws \<Longrightarrow> utf8_valid (ws @ [w])\<close>
proof (induction ws)
  case Nil
  then show ?case
    by (simp add: utf8_valid_one_byte) 
next
  case (Cons w' ws)

  show ?case
    using Cons.prems(2)
    by (induction rule: utf8_valid.induct, auto simp add: Cons.prems(1) utf8_valid_empty
      utf8_valid_one_byte utf8_valid_two_bytes utf8_valid_three_bytes utf8_valid_four_bytes) 
qed

lemma utf8_valid_two_byte_snoc: \<open>is_two_bytes w1 w2 \<Longrightarrow> utf8_valid ws \<Longrightarrow> utf8_valid (ws @ [w1, w2])\<close>
proof (induction ws) 
  case Nil
  then show ?case
    by (simp add: utf8_valid_two_bytes) 
next
  case (Cons w' ws)

  show ?case
    using Cons.prems(2)
    by (induction rule: utf8_valid.induct, auto simp add: Cons.prems(1) utf8_valid_empty
      utf8_valid_one_byte utf8_valid_two_bytes utf8_valid_three_bytes utf8_valid_four_bytes) 
qed 

lemma utf8_valid_three_byte_snoc:
  \<open>is_three_bytes w1 w2 w3 \<Longrightarrow> utf8_valid ws \<Longrightarrow> utf8_valid (ws @ [w1, w2, w3])\<close>
proof (induction ws) 
  case Nil
  then show ?case
    by (simp add: utf8_valid_three_bytes) 
next
  case (Cons w' ws)

  show ?case
    using Cons.prems(2)
    by (induction rule: utf8_valid.induct, auto simp add: Cons.prems(1) utf8_valid_empty
      utf8_valid_one_byte utf8_valid_two_bytes utf8_valid_three_bytes utf8_valid_four_bytes) 
qed 

lemma utf8_valid_four_bytes_snow:
  \<open>is_four_bytes w1 w2 w3 w4 \<Longrightarrow> utf8_valid ws \<Longrightarrow> utf8_valid (ws @ [w1, w2, w3, w4])\<close>
proof (induction ws) 
  case Nil
  then show ?case
    by (simp add: utf8_valid_four_bytes) 
next
  case (Cons w' ws)

  show ?case
    using Cons.prems(2)
    by (induction rule: utf8_valid.induct, auto simp add: Cons.prems(1) utf8_valid_empty
      utf8_valid_one_byte utf8_valid_two_bytes utf8_valid_three_bytes utf8_valid_four_bytes) 
qed 

section \<open>UTF-8 high-level parser\<close>

definition cond_decode_utf8 :: \<open>byte_string \<times> codepoint_string option \<Rightarrow> bool\<close> where
  \<open>cond_decode_utf8 x \<equiv> case x of
    (_, None) \<Rightarrow> False
  | (bs, Some  _) \<Rightarrow> bs \<noteq> []\<close> 

definition invar_decode_utf8 :: \<open>byte_string \<Rightarrow> byte_string \<times> codepoint_string option \<Rightarrow> bool\<close> where
  \<open>invar_decode_utf8 bs x \<equiv> case x of
    (_, None) \<Rightarrow> True
  | (bs', Some _) \<Rightarrow> utf8_valid (take (length bs - length bs') bs) \<and>
    drop (length bs - length bs') bs = bs'\<close> 

definition decode_utf8 :: \<open>byte_string \<Rightarrow> codepoint_string option nres\<close> where
  \<open>decode_utf8 bs \<equiv> do {
    (_, st) \<leftarrow> WHILE\<^sub>T\<^bsup>invar_decode_utf8 bs\<^esup> cond_decode_utf8 (\<lambda> st. case st of
        (bs, None) \<Rightarrow> RETURN (bs, None)
      | (bs, Some rs) \<Rightarrow> (case bs of
        [] \<Rightarrow> RETURN ([], Some rs)
      | w # ws \<Rightarrow>
        if \<not> bit w 7
            \<comment>\<open>One-byte conduct\<close>
        then RETURN (ws, Some (rs @ [word8_to_word24 (take_bit 6 w)]))
        else if bit w 7 \<and> bit w 6 \<and> \<not> bit w 5
            \<comment>\<open>Two-byte sequence\<close>
        then case ws of
          w' # ws' \<Rightarrow>
          if bit w' 7 \<and> \<not> bit w' 6 \<and> two_byte_codepoint w w' > 0x7F
          then RETURN (ws', Some (rs @ [two_byte_codepoint w w']))
          else RETURN (ws, None)
            \<comment>\<open>Continuation byte is incorrect\<close>
        | _ \<Rightarrow> RETURN (ws, None)
            \<comment>\<open>No continuation byte (EOF found)\<close>
        else if bit w 7 \<and> bit w 6 \<and> bit w 5 \<and> \<not> bit w 4
            \<comment>\<open>Three-byte sequence\<close>
        then case ws of
          w' # w'' # ws' \<Rightarrow>
          if bit w' 7 \<and> \<not> bit w' 6 \<and> bit w'' 7 \<and> \<not> bit w'' 6 \<and> three_byte_codepoint w w' w'' > 0x7FF
          then RETURN (ws', Some (rs @ [three_byte_codepoint w w' w'']))
          else RETURN (ws, None)
            \<comment>\<open>Continuation bytes are incorrect\<close>
       | _ \<Rightarrow> RETURN (ws, None)
            \<comment>\<open>Not enough continuation bytes (EOF found too early)\<close>
       else if bit w 7 \<and> bit w 6 \<and> bit w 5 \<and> bit w 4 \<and> \<not> bit w 3
            \<comment>\<open>Four-byte sequence\<close>
       then case ws of
         w' # w'' # w''' # ws' \<Rightarrow>
         if bit w' 7 \<and> \<not> bit w' 6 \<and> bit w'' 7 \<and> \<not> bit w'' 6 \<and> bit w''' 7 \<and> \<not> bit w''' 6 \<and>
            four_byte_codepoint w w' w'' w''' > 0xFFFF
         then RETURN (ws', Some (rs @ [four_byte_codepoint w w' w'' w''']))
         else RETURN (ws, None)
           \<comment>\<open>Continuation bytes are incorrect\<close>
       | _ \<Rightarrow> RETURN (ws, None)
           \<comment>\<open>Not enough continuation bytes (EOF found too early)\<close>
       else RETURN (ws, None)
           \<comment>\<open>Incorrect byte\<close>)
    ) (bs, Some []);
    RETURN st
  }\<close> 

abbreviation termination_decode_utf8 :: \<open>(byte_string \<times> codepoint_string option) rel\<close> where
  \<open>termination_decode_utf8 \<equiv> measure (length \<circ> fst)\<close> 

lemma invar_decode_utf8_init: \<open>invar_decode_utf8 bs (bs, Some [])\<close>
  unfolding invar_decode_utf8_def
  using utf8_valid_empty
  by auto

lemma invar_decode_utf8_step1: \<open>invar_decode_utf8 bs (bs', None)\<close>
  unfolding invar_decode_utf8_def
  by fastforce 

lemma invar_decode_utf8_step2:
  assumes
    invar: \<open>invar_decode_utf8 bs (bs', Some rs)\<close> and
    is_one_byte_w: \<open>is_one_byte w\<close> and
    bs'_is: \<open>bs' = w # ws\<close> 
  shows
    \<open>invar_decode_utf8 bs (ws, Some (rs @ [word8_to_word24 (take_bit 6 w)]))\<close>
proof -
  have
    \<open>utf8_valid (take (length bs - length bs') bs)\<close> and
    invar_drop: \<open>drop (length bs - length bs') bs = bs'\<close>
    using invar
    unfolding invar_decode_utf8_def
    by fastforce+
  then have
    \<open>utf8_valid (take (length bs - length bs') bs @ [w])\<close> and
    invar_drop': \<open>drop (length bs - (length bs' - 1)) bs = ws\<close>
    by (fastforce simp: utf8_valid_one_byte_snoc[OF is_one_byte_w],
        metis (mono_tags, lifting) One_nat_def Suc_diff bs'_is diff_le_self drop_eq_ConsD
        length_drop length_ge_1_conv list.simps(3))  
  then have \<open>utf8_valid (take (length bs - length ws) bs)\<close>
    using bs'_is invar_drop
    by (smt (verit, del_insts) Suc_diff_Suc diff_less gr0I length_Cons length_greater_0_conv
        list.sel(1) list.simps(3) take_eq_Nil take_hd_drop utf8_valid.simps zero_less_diff) 
  then show ?thesis
    unfolding invar_decode_utf8_def 
    using invar_drop'
    by auto
qed

lemma invar_decode_utf8_step3:
  assumes
    invar: \<open>invar_decode_utf8 bs (bs', Some rs)\<close> and
    bits_w: \<open>bit w 7\<close> \<open>bit w 6\<close> \<open>\<not> bit w 5\<close> and
    bs'_is: \<open>bs' = w # ws\<close>
  shows 
    \<open>(case ws of
      [] \<Rightarrow> RETURN (ws, None)
    | w' # ws' \<Rightarrow>
      if bit w' 7 \<and> \<not> bit w' 6 \<and> 127 < two_byte_codepoint w w'
      then RETURN (ws', Some (rs @ [two_byte_codepoint w w']))
      else RETURN (ws, None))
   \<le> SPEC (\<lambda> s'. invar_decode_utf8 bs s' \<and> length (fst s') < Suc (length ws))\<close>
proof (cases ws) 
  case Nil
  then show ?thesis
    using invar_decode_utf8_step1
    by force
next
  case (Cons w' ws')
  then show ?thesis
  proof (auto intro: invar_decode_utf8_step1) 
    assume
      ws_is: \<open>ws = w' # ws'\<close> and 
      bits_w': \<open>bit w' 7\<close> \<open>\<not> bit w' 6\<close> and
      codepoint_limit: \<open>127 < two_byte_codepoint w w'\<close>

    have bs'_is: \<open>bs' = w # w' # ws'\<close>
      using bs'_is ws_is
      by blast
    then have length_ws'_is: \<open>length bs' - 2 = length ws'\<close>
      by simp 

    have
      \<open>utf8_valid (take (length bs - length bs') bs)\<close> and
      invar_drop: \<open>drop (length bs - length bs') bs = bs'\<close>
      using invar
      unfolding invar_decode_utf8_def
      by fastforce+
    then have
      \<open>utf8_valid (take (length bs - length bs') bs @ [w, w'])\<close> and
      invar_drop': \<open>drop (length bs - (length bs' - 2)) bs = ws'\<close>
      by (fastforce simp: bits_w bits_w' codepoint_limit is_continuation_byte_def
          utf8_valid_two_byte_snoc,
          smt (verit, best) Suc_diff_Suc bs'_is diff_le_self diff_less drop_0 drop_Cons_numeral
          drop_eq_ConsD le_add_diff_inverse length_drop length_greater_0_conv less_one nat_numeral
          nat_numeral_diff_1 numeral_BitM numerals(1) semiring_norm(26) trans_less_add1 ws_is) 
    then have \<open>utf8_valid (take (length bs - length ws') bs)\<close>
    proof -
      assume hyp: \<open>utf8_valid (take (length bs - length bs') bs @ [w, w'])\<close> 

      obtain bs'' where
        bs_is: \<open>bs = bs'' @ w # w' # ws'\<close> and
        length_bs''_eq: \<open>length bs'' = length bs - length bs'\<close>
        by (metis add_diff_cancel_right' append_take_drop_id assms(5) invar_drop length_append ws_is)
      then have take_n_is_bs'': \<open>take (length bs - length bs') bs = bs''\<close>
        by auto 
      then have \<open>take (length bs - length bs' + 1) bs = bs'' @ [w]\<close>
        by (simp add: bs'_is bs_is) 
      then have \<open>take (length bs - length bs' + 2) bs = bs'' @ [w, w']\<close>
        by (metis take_n_is_bs'' bs'_is invar_drop numerals(2) take_Suc_Cons take_add take_eq_Nil) 
      then have \<open>take (length bs - length ws') bs = bs'' @ [w, w']\<close>
        using length_ws'_is
        by (simp add: assms(5) bs_is ws_is) 
      then show \<open>utf8_valid (take (length bs - length ws') bs)\<close>
        using hyp take_n_is_bs''
        by auto
    qed  
    then show \<open>invar_decode_utf8 bs (ws', Some (rs @ [two_byte_codepoint w w']))\<close>
      unfolding invar_decode_utf8_def
      using invar_drop'
      by auto 
  qed
qed

(* Somehow @{thm numerals} only goes up to \<open>2\<close>. *)
lemma numerals_3: \<open>3 = Suc (Suc (Suc 0))\<close>
  by linarith 

lemma numerals_4: \<open>4 = Suc (Suc (Suc (Suc 0)))\<close>
  by linarith

lemma invar_decode_utf8_step4:
  assumes
    invar: \<open>invar_decode_utf8 bs (bs', Some rs)\<close> and 
    bits_w: \<open>bit w 7\<close> \<open>bit w 6\<close> \<open>bit w 5\<close> \<open>\<not> bit w 4\<close> and 
    bs'_is: \<open>bs' = w # ws\<close>
  shows 
    \<open>(case ws of
      [] \<Rightarrow> RETURN (ws, None)
    | [w'] \<Rightarrow> RETURN (ws, None)
    | w' # w'' # ws' \<Rightarrow>
      if bit w' 7 \<and> \<not> bit w' 6 \<and> bit w'' 7 \<and> \<not> bit w'' 6 \<and> 2047 < three_byte_codepoint w w' w''
      then RETURN (ws', Some (rs @ [three_byte_codepoint w w' w'']))
      else RETURN (ws, None))
    \<le> SPEC (\<lambda> s'. invar_decode_utf8 bs s' \<and> length (fst s') < Suc (length ws))\<close>
proof (cases ws) 
  case Nil
  then show ?thesis
    by (simp add: invar_decode_utf8_step1) 
next
  case Cons1: (Cons w' ws')

  show ?thesis
  proof (cases ws')
    case Nil
    then show ?thesis
      using Cons1
      by (simp add: invar_decode_utf8_step1) 
  next
    case (Cons w'' ws'')
    then show ?thesis
    proof (auto simp add: Cons1 intro: invar_decode_utf8_step1)
      assume
        bits_w': \<open>bit w' 7\<close> \<open>\<not> bit w' 6\<close> and 
        bits_w'': \<open>bit w'' 7\<close> \<open>\<not> bit w'' 6\<close> and 
        codepoint_limit: \<open>2047 < three_byte_codepoint w w' w''\<close>

      obtain bs'' where
        bs_is: \<open>bs = bs'' @ w # w' # w'' # ws''\<close> and
        take_n_bs_is_bs'': \<open>take (length bs - length bs') bs = bs''\<close>
        by (smt (verit, ccfv_SIG) Cons1 append_take_drop_id bs'_is invar invar_decode_utf8_def
            local.Cons option.case(2) split_conv)

      have
        valid_bs: \<open>utf8_valid (take (length bs - length bs') bs)\<close> and
        drop_bs: \<open>drop (length bs - length bs') bs = bs'\<close> 
        using invar
        unfolding invar_decode_utf8_def
        by fastforce+
      then have \<open>take (length bs - length bs' + 1) bs = bs'' @ [w]\<close>
        by (metis One_nat_def add.right_neutral add_Suc_right append_is_Nil_conv bs'_is bs_is
            diff_less length_greater_0_conv list.sel(1) list.simps(3) take_hd_drop take_n_bs_is_bs'') 
      then have \<open>take (length bs - length bs' + 2) bs = bs'' @ [w, w']\<close>
        by (metis Cons1 bs'_is drop_bs numerals(2) take_Suc_Cons take_add take_eq_Nil
            take_n_bs_is_bs'') 
      then have \<open>take (length bs - length bs' + 3) bs = bs'' @ [w, w', w'']\<close>
        using bs_is drop_bs Cons1 bs'_is take_Suc_Cons numerals_3
        by (simp add: local.Cons) 
      then have \<open>utf8_valid (take (length bs - (length bs' - 3)) bs)\<close>
        using valid_bs utf8_valid_three_byte_snoc bits_w bits_w' bits_w'' codepoint_limit
        by (smt (verit, del_insts) add_diff_cancel_right' diff_diff_left drop_all drop_bs
            is_continuation_byte_def le_add_diff_inverse length_drop nat_le_linear take_all
            take_n_bs_is_bs'')
      then have valid_bs: \<open>utf8_valid (take (length bs - length ws'') bs)\<close>
        by (simp add: Cons1 bs'_is local.Cons) 

      have \<open>drop (length bs - (length bs' - 3)) bs = ws''\<close>
        using drop_bs bs_is bs'_is Cons1 Cons
        by simp 
      then have \<open>drop (length bs - length ws'') bs = ws''\<close>
        by (metis diff_diff_cancel diff_le_self length_drop) 
      then show \<open>invar_decode_utf8 bs (ws'', Some (rs @ [three_byte_codepoint w w' w'']))\<close> 
        unfolding invar_decode_utf8_def
        using valid_bs
        by fastforce
    qed
  qed
qed

lemma invar_decode_utf8_step5:
  assumes
    invar: \<open>invar_decode_utf8 bs (bs', Some rs)\<close> and
    bits_w: \<open>bit w 7\<close> \<open>bit w 6\<close> \<open>bit w 5\<close> \<open>bit w 4\<close> \<open>\<not> bit w 3\<close> and
    bs'_is: \<open>bs' = w # ws\<close> 
  shows
    \<open>(case ws of
      [] \<Rightarrow> RETURN (ws, None)
    | [w'] \<Rightarrow> RETURN (ws, None)
    | [w', w''] \<Rightarrow> RETURN (ws, None)
    | w' # w'' # w''' # ws' \<Rightarrow>
      if bit w' 7 \<and> \<not> bit w' 6 \<and> bit w'' 7 \<and> \<not> bit w'' 6 \<and> bit w''' 7 \<and> \<not> bit w''' 6 \<and>
         65535 < four_byte_codepoint w w' w'' w'''
      then RETURN (ws', Some (rs @ [four_byte_codepoint w w' w'' w''']))
      else RETURN (ws, None))
    \<le> SPEC (\<lambda> s'. invar_decode_utf8 bs s' \<and> length (fst s') < Suc (length ws))\<close>
proof (cases ws) 
  case Nil
  then show ?thesis
    by (simp add: invar_decode_utf8_step1) 
next
  case Cons1: (Cons w' ws')

  show ?thesis
  proof (cases ws')
    case Nil
    then show ?thesis
      using Cons1
      by (simp add: invar_decode_utf8_step1) 
  next
    case Cons2: (Cons w'' ws'')

    show ?thesis
    proof (cases ws'') 
      case Nil
      then show ?thesis
        using Cons1 Cons2
        by (simp add: invar_decode_utf8_step1)  
    next
      case (Cons w''' ws''')
      then show ?thesis
      proof (auto simp add: Cons1 Cons2 intro: invar_decode_utf8_step1) 
        assume
          bits_w': \<open>bit w' 7\<close> \<open>\<not> bit w' 6\<close> and 
          bits_w'': \<open>bit w'' 7\<close> \<open>\<not> bit w'' 6\<close> and 
          bits_w''': \<open>bit w''' 7\<close> \<open>\<not> bit w''' 6\<close> and 
          codepoint_limit: \<open>65535 < four_byte_codepoint w w' w'' w'''\<close>

        have length_ws'''_is: \<open>length ws''' = length bs' - 4\<close>
          using Cons Cons2 Cons1 bs'_is
          by simp 

        obtain bs'' where
          bs_is: \<open>bs = bs'' @ w # w' # w'' # w''' # ws'''\<close> and
          take_n_is_bs'': \<open>take (length bs - length bs') bs = bs''\<close>
          by (smt (verit, del_insts) Cons1 Cons2 append_take_drop_id assms(7) invar
              invar_decode_utf8_def local.Cons option.case(2) split_conv) 

        have \<open>utf8_valid (take (length bs - length bs') bs)\<close>
          using invar
          unfolding invar_decode_utf8_def
          by fastforce
        moreover have \<open>take (length bs - length bs' + 1) bs = bs'' @ [w]\<close>
          using take_n_is_bs'' bs_is
          by (metis (no_types, lifting) Nil_is_append_conv Suc_eq_plus1 append_eq_append_conv
              append_take_drop_id bs'_is diff_less length_greater_0_conv list.discI list.sel(1)
              take_hd_drop)
        then have \<open>take (length bs - length bs' + 2) bs = bs'' @ [w, w']\<close>
          by (metis (no_types, lifting) add_diff_cancel_right' append_take_drop_id bs_is
              cancel_comm_monoid_add_class.diff_cancel nat_1_add_1 numerals(1) same_append_eq
              take_Cons_numeral take_add take_eq_Nil take_n_is_bs'')
        then have \<open>take (length bs - length bs' + 3) bs = bs'' @ [w, w', w'']\<close>
          by (smt (verit, best) append_take_drop_id bs_is numerals_3 same_append_eq take_Suc_Cons
              take_add take_eq_Nil take_n_is_bs'')
        then have \<open>take (length bs - length bs' + 4) bs = bs'' @ [w, w', w'', w''']\<close>
          using numerals_4 bs_is take_n_is_bs''
          by (metis (no_types, opaque_lifting) Cons2 append_take_drop_id local.Cons same_append_eq
              take_Suc_Cons take_add take_eq_Nil2) 
        then have \<open>take (length bs - length ws''') bs = bs'' @ [w, w', w'', w''']\<close>
          using Cons1 Cons2 bs'_is bs_is local.Cons
          by auto
        ultimately have \<open>utf8_valid (take (length bs - length ws''') bs)\<close>
          by (simp add: bits_w''' bits_w'' bits_w' bits_w codepoint_limit is_continuation_byte_def
              take_n_is_bs'' utf8_valid_four_bytes_snow)
        moreover have \<open>drop (length bs - length bs') bs = bs'\<close>
          using invar
          unfolding invar_decode_utf8_def
          by fastforce
        then have \<open>drop (length bs - length bs' + 4) bs = ws'''\<close> 
          using Cons Cons1 Cons2 bs'_is bs_is
          by simp 
        then have \<open>drop (length bs - length ws''') bs = ws'''\<close>
          using length_ws'''_is
          by (metis add_diff_cancel_right' append_eq_conv_conj append_take_drop_id length_append) 
        ultimately show \<open>invar_decode_utf8 bs (ws''', Some (rs @ [four_byte_codepoint w w' w'' w''']))\<close>
          unfolding invar_decode_utf8_def
          by auto 
      qed
    qed
  qed
qed

theorem decode_utf8_correct: \<open>decode_utf8 bs \<le> SPEC (case_option True (\<lambda>_. utf8_valid bs))\<close>
  unfolding decode_utf8_def
proof (refine_vcg WHILEIT_rule[where R=\<open>termination_decode_utf8\<close>], auto)
  show \<open>invar_decode_utf8 bs (bs, Some [])\<close>
    by (fact invar_decode_utf8_init) 
next 
  fix bs' 
  assume \<open>cond_decode_utf8 (bs', None)\<close> 
  then show \<open>False\<close>
    unfolding cond_decode_utf8_def
    by simp 
next
  fix bs' rs
  assume
    invar: \<open>invar_decode_utf8 bs (bs', Some rs)\<close> and
    cond: \<open>cond_decode_utf8 (bs', Some rs)\<close>  

  then show
    \<open>(case bs' of
       [] \<Rightarrow> RETURN ([], Some rs)
     | w # ws \<Rightarrow>
       if is_one_byte w
       then RETURN (ws, Some (rs @ [word8_to_word24 (take_bit 6 w)]))
       else if bit w 7 \<and> bit w 6 \<and> \<not> bit w 5
       then case ws of
         [] \<Rightarrow> RETURN (ws, None)
       | w' # ws' \<Rightarrow>
         if bit w' 7 \<and> \<not> bit w' 6 \<and> 127 < two_byte_codepoint w w'
         then RETURN (ws', Some (rs @ [two_byte_codepoint w w']))
         else RETURN (ws, None)
       else if bit w 7 \<and> bit w 6 \<and> bit w 5 \<and> \<not> bit w 4
       then case ws of
         [] \<Rightarrow> RETURN (ws, None)
       | [w'] \<Rightarrow> RETURN (ws, None)
       | w' # w'' # ws' \<Rightarrow>
         if bit w' 7 \<and> \<not> bit w' 6 \<and> bit w'' 7 \<and> \<not> bit w'' 6 \<and> 2047 < three_byte_codepoint w w' w''
         then RETURN (ws', Some (rs @ [three_byte_codepoint w w' w'']))
         else RETURN (ws, None)
       else if bit w 7 \<and> bit w 6 \<and> bit w 5 \<and> bit w 4 \<and> \<not> bit w 3
       then case ws of
         [] \<Rightarrow> RETURN (ws, None)
       | [w'] \<Rightarrow> RETURN (ws, None)
       | [w', w''] \<Rightarrow> RETURN (ws, None)
       | w' # w'' # w''' # ws' \<Rightarrow>
         if bit w' 7 \<and> \<not> bit w' 6 \<and> bit w'' 7 \<and> \<not> bit w'' 6 \<and> bit w''' 7 \<and> \<not> bit w''' 6 \<and>
            65535 < four_byte_codepoint w w' w'' w'''
         then RETURN (ws', Some (rs @ [four_byte_codepoint w w' w'' w''']))
         else RETURN (ws, None)
      else RETURN (ws, None))
    \<le> SPEC (\<lambda> s'. invar_decode_utf8 bs s' \<and> length (fst s') < length bs')\<close>
  proof (cases bs') 
    case Nil
    then show ?thesis
      using cond cond_decode_utf8_def 
      by auto  
  next
    case (Cons w ws)
    then show ?thesis 
      by (auto intro: invar_decode_utf8_step1 invar_decode_utf8_step2[OF invar]
          invar_decode_utf8_step3[OF invar] invar_decode_utf8_step4[OF invar]
          invar_decode_utf8_step5[OF invar])
  qed 
next
  fix bs' rs
  assume
    invar: \<open>invar_decode_utf8 bs (bs', rs)\<close> and
    cond: \<open>\<not> cond_decode_utf8 (bs', rs)\<close>
  then show \<open>case rs of None \<Rightarrow> True | Some _ \<Rightarrow> utf8_valid bs\<close>
    unfolding cond_decode_utf8_def invar_decode_utf8_def
    using case_optionE
    by fastforce 
qed

section \<open>UTF-8 lower-level parser\<close>

text \<open>
  Instead of recursively iterating through the list, we iterate through the list by indexing into it.
  This will make it easier later on to refine even more this algorithm.
\<close>

definition invar_decode_utf8_2 :: \<open>nat \<Rightarrow> byte_string \<Rightarrow> (nat \<times> codepoint_string option) \<Rightarrow> bool\<close> where
  \<open>invar_decode_utf8_2 n bs x \<equiv> case x of
  (i, st) \<Rightarrow> i \<le> n \<and> case_option True (\<lambda> _. utf8_valid (take i bs)) st\<close> 

definition cond_decode_utf8_2 :: \<open>nat \<Rightarrow> (nat \<times> codepoint_string option) \<Rightarrow> bool\<close> where
  \<open>cond_decode_utf8_2 n x \<equiv> case x of
    (i, st) \<Rightarrow> i < n \<and> st \<noteq> None\<close> 

text \<open>
  Trying to decode a codepoint of the form \<^verbatim>\<open>0xxxxxxx\<close>.
\<close> 

definition decode_one_byte :: \<open>byte_string \<Rightarrow> nat \<Rightarrow> (nat \<times> uint32 option) nres\<close> where
  \<open>decode_one_byte bs i \<equiv>
    if length bs \<le> i \<or> bit (bs ! i) 7
    then RETURN (i + 1, None)
    else RETURN (i + 1, Some (word8_to_word24 (take_bit 6 (bs ! i))))\<close>

lemma decode_one_byte_correct:
  \<open>decode_one_byte bs i
  \<le> SPEC (\<lambda> (i', r). case_option (length bs \<le> i \<or> \<not> is_one_byte (bs ! i))
    (\<lambda> cp. i < length bs \<and> is_one_byte (bs ! i) \<and> cp = word8_to_word24 (take_bit 6 (bs ! i)) \<and>
    i' = i + 1) r)\<close>
  unfolding decode_one_byte_def
  by (refine_vcg, auto)

text \<open>
  Trying to decode a codepoint of the form \<^verbatim>\<open>110xxxxx 10xxxxxx\<close>. 
\<close> 

definition decode_two_bytes :: \<open>byte_string \<Rightarrow> nat \<Rightarrow> (nat \<times> uint32 option) nres\<close> where
  \<open>decode_two_bytes bs i \<equiv>
    if length bs \<le> Suc i \<or> \<not> bit (bs ! i) 7 \<or> \<not> bit (bs ! i) 6 \<or> bit (bs ! i) 5 \<or>
       \<not> bit (bs ! Suc i) 7 \<or> bit (bs ! Suc i) 6 \<or> two_byte_codepoint (bs ! i) (bs ! Suc i) \<le> 0x7F
    then RETURN (i + 1, None)
    else RETURN (i + 2, Some (two_byte_codepoint (bs ! i) (bs ! Suc i)))\<close>

lemma decode_two_bytes_correct:
  \<open>decode_two_bytes bs i
  \<le> SPEC (\<lambda> (i', r). case_option (length bs \<le> Suc i \<or> \<not> is_two_bytes (bs ! i) (bs ! Suc i))
    (\<lambda> cp. Suc i < length bs \<and> is_two_bytes (bs ! i) (bs ! Suc i) \<and>
    cp = two_byte_codepoint (bs ! i) (bs ! Suc i) \<and> i' = i + 2) r)\<close> 
  unfolding decode_two_bytes_def is_continuation_byte_def
  by (refine_vcg, auto) 

text \<open>
  Trying to decode a codepoint of the form \<^verbatim>\<open>1110xxxx 10xxxxxx 10xxxxxx\<close>. 
\<close> 

definition decode_three_bytes :: \<open>byte_string \<Rightarrow> nat \<Rightarrow> (nat \<times> uint32 option) nres\<close> where
  \<open>decode_three_bytes bs i \<equiv>
    if length bs \<le> Suc (Suc i) \<or> \<not> bit (bs ! i) 7 \<or> \<not> bit (bs ! i) 6 \<or> \<not> bit (bs ! i) 5 \<or>
       bit (bs ! i) 4 \<or> \<not> bit (bs ! Suc i) 7 \<or> bit (bs ! Suc i) 6 \<or> \<not> bit (bs ! Suc (Suc i)) 7 \<or>
       bit (bs ! Suc (Suc i)) 6 \<or>
       three_byte_codepoint (bs ! i) (bs ! Suc i) (bs ! Suc (Suc i)) \<le> 0x7FF
    then RETURN (i + 1, None)
    else RETURN (i + 3, Some (three_byte_codepoint (bs ! i) (bs ! Suc i) (bs ! Suc (Suc i))))\<close>

lemma decode_three_bytes_correct:
  \<open>decode_three_bytes bs i
  \<le> SPEC (\<lambda> (i', r). case_option
    (length bs \<le> Suc (Suc i) \<or> \<not> is_three_bytes (bs ! i) (bs ! Suc i) (bs ! Suc (Suc i)))
    (\<lambda> cp. Suc (Suc i) < length bs \<and> is_three_bytes (bs ! i) (bs ! Suc i) (bs ! Suc (Suc i)) \<and>
    cp = three_byte_codepoint (bs ! i) (bs ! Suc i) (bs ! Suc (Suc i)) \<and> i' = i + 3) r)\<close>
  unfolding decode_three_bytes_def is_continuation_byte_def
  by (refine_vcg, auto) 

text \<open>
  Trying to decode a codepoint of the form \<^verbatim>\<open>11110xxx 10xxxxxx 10xxxxxx 10xxxxxx\<close>.
\<close> 

definition decode_four_bytes :: \<open>byte_string \<Rightarrow> nat \<Rightarrow> (nat \<times> uint32 option) nres\<close> where
  \<open>decode_four_bytes bs i \<equiv>
    if length bs \<le> Suc (Suc (Suc i)) \<or> \<not> bit (bs ! i) 7 \<or> \<not> bit (bs ! i) 6 \<or> \<not> bit (bs ! i) 5 \<or>
       \<not> bit (bs ! i) 4 \<or> bit (bs ! i) 3 \<or> \<not> bit (bs ! Suc i) 7 \<or> bit (bs ! Suc i) 6 \<or>
       \<not> bit (bs ! Suc (Suc i)) 7 \<or> bit (bs ! Suc (Suc i)) 6 \<or> \<not> bit (bs ! Suc (Suc (Suc i))) 7 \<or>
       bit (bs ! Suc (Suc (Suc i))) 6 \<or>
       four_byte_codepoint (bs ! i) (bs ! Suc i) (bs ! Suc (Suc i)) (bs ! Suc (Suc (Suc i))) \<le> 0xFFFF
    then RETURN (i + 1, None)
    else RETURN (i + 4, Some (four_byte_codepoint (bs ! i) (bs ! Suc i) (bs ! Suc (Suc i))
      (bs ! Suc (Suc (Suc i)))))\<close> 

lemma decode_four_bytes_correct:
  \<open>decode_four_bytes bs i
  \<le> SPEC (\<lambda> (i', r). case_option
    (length bs \<le> Suc (Suc (Suc i)) \<or>
      \<not> is_four_bytes (bs ! i) (bs ! Suc i) (bs ! Suc (Suc i)) (bs ! Suc (Suc (Suc i))))
    (\<lambda> cp. Suc (Suc (Suc i)) < length bs \<and>
    is_four_bytes (bs ! i) (bs ! Suc i) (bs ! Suc (Suc i)) (bs ! Suc (Suc (Suc i))) \<and>
    cp = four_byte_codepoint (bs ! i) (bs ! Suc i) (bs ! Suc (Suc i)) (bs ! Suc (Suc (Suc i))) \<and>
    i' = i + 4) r)\<close>
  unfolding decode_four_bytes_def is_continuation_byte_def
  by (refine_vcg, auto) 

definition decode_utf8_2 :: \<open>byte_string \<Rightarrow> codepoint_string option nres\<close> where
  \<open>decode_utf8_2 bs \<equiv> do {
    (_, st) \<leftarrow> WHILE\<^sub>T\<^bsup>invar_decode_utf8_2 (length bs) bs\<^esup> (cond_decode_utf8_2 (length bs)) (\<lambda> (i, st). case st of
      None \<Rightarrow> RETURN (i, None)
    | Some ws \<Rightarrow> do {
      res \<leftarrow> decode_one_byte bs i;
      case res of
        (i, Some cp) \<Rightarrow> RETURN (i, Some (ws @ [cp]))
      | (_, None) \<Rightarrow> do {
        res \<leftarrow> decode_two_bytes bs i;
        case res of
          (i, Some cp) \<Rightarrow> RETURN (i, Some (ws @ [cp]))
        | (_, None) \<Rightarrow> do {
          res \<leftarrow> decode_three_bytes bs i;
          case res of
            (i, Some cp) \<Rightarrow> RETURN (i, Some (ws @ [cp]))
          | (_, None) \<Rightarrow> do {
            res \<leftarrow> decode_four_bytes bs i;
            case res of
              (i, Some cp) \<Rightarrow> RETURN (i, Some (ws @ [cp]))
            | (_, None) \<Rightarrow> RETURN (i + 1, None)
          }
        }
      }
    }) (0, Some []);
    RETURN st
  }\<close>

abbreviation termination_decode_utf8_2 :: \<open>nat \<Rightarrow> (nat \<times> codepoint_string option) rel\<close> where
  \<open>termination_decode_utf8_2 n \<equiv> measure (\<lambda> (i, _). n - i)\<close>

abbreviation st_refine
  :: \<open>nat \<Rightarrow> ((nat \<times> codepoint_string option) \<times> (byte_string \<times> codepoint_string option)) set\<close> where
  \<open>st_refine n \<equiv> { ((i, rs), (bs', rs)) | i bs' rs. length bs' + i = n }\<close> 

lemma invar_decode_utf8_2_if:
  assumes
    st_refine: \<open>(st, st') \<in> st_refine (length bs)\<close> and
    invar: \<open>invar_decode_utf8 bs st'\<close>
  shows
    \<open>invar_decode_utf8_2 (length bs) bs st\<close>
proof -
  have res_eq: \<open>snd st = snd st'\<close>
    using st_refine
    by fastforce 

  have \<open>length (fst st') + fst st = length bs\<close>
    using st_refine
    by auto
  then have fst_st_eq: \<open>fst st = length bs - length (fst st')\<close>
    by linarith 
  then have \<open>fst st \<le> length bs\<close>
    by linarith 
  moreover have
    \<open>snd st = Some rs \<Longrightarrow> snd st' = Some rs \<Longrightarrow> utf8_valid (take (fst st) bs)\<close>
    for rs
  proof -
    assume
      st'_res_eq: \<open>snd st = Some rs\<close> and
      st_res_eq: \<open>snd st' = Some rs\<close> 

    show \<open>utf8_valid (take (fst st) bs)\<close>
      using invar st_res_eq fst_st_eq
      unfolding invar_decode_utf8_def
      by auto 
  qed
  ultimately show \<open>invar_decode_utf8_2 (length bs) bs st\<close>
    unfolding invar_decode_utf8_def invar_decode_utf8_2_def
    using res_eq case_optionE case_prodE
    by (smt (verit, del_insts) case_prod_unfold invar invar_decode_utf8_def option.simps(4)
        option.simps(5))   
qed 

lemma cond_decode_utf8_2_if:
  assumes
    invar2: \<open>invar_decode_utf8_2 (length bs) bs (i, rs)\<close> and 
    invar: \<open>invar_decode_utf8 bs (bs', rs)\<close> and 
    \<open>length bs' + i = length bs\<close> and 
    cond: \<open>cond_decode_utf8 (bs', rs)\<close>
  shows
    \<open>cond_decode_utf8_2 (length bs) (i, rs)\<close> 
  using assms
  unfolding cond_decode_utf8_def cond_decode_utf8_2_def 
  using case_optionE nat_neq_iff rec_prod_is_case
  by fastforce

lemma cond_decode_utf8_if:
  assumes
    \<open>invar_decode_utf8_2 (length bs) bs (i, rs)\<close> and
    \<open>invar_decode_utf8 bs (bs', rs)\<close> and
    \<open>length bs' + i = length bs\<close> and
    \<open>cond_decode_utf8_2 (length bs) (i, rs)\<close>
  shows
    \<open>cond_decode_utf8 (bs', rs)\<close>
  using assms
  unfolding cond_decode_utf8_def cond_decode_utf8_2_def
  by fastforce

lemma cond_decode_utf8_iff_cond_decode_utf8_2:
  assumes
    \<open>(st, st') \<in> st_refine (length bs)\<close> and 
    \<open>invar_decode_utf8_2 (length bs) bs st\<close> and 
    \<open>invar_decode_utf8 bs st'\<close>
  shows
    \<open>cond_decode_utf8_2 (length bs) st \<longleftrightarrow> cond_decode_utf8 st'\<close>
  using cond_decode_utf8_if cond_decode_utf8_2_if assms
  by blast 

text \<open>
  These abbreviations are just to avoid writing the same thing over and over (and to make
  proof states readable).
\<close> 

abbreviation
  \<open>st_refine' n \<equiv> {x. \<exists> i bs'. (\<exists> rs. x = ((i, rs), bs', rs)) \<and> length bs' + i = n}\<close>

abbreviation
  \<open>decode_utf8_body bs rs \<equiv>
    (case bs of
      [] \<Rightarrow> RETURN ([], Some rs)
    | w # ws \<Rightarrow>
      if is_one_byte w
      then RETURN (ws, Some (rs @ [word8_to_word24 (take_bit 6 w)]))
      else if bit w 7 \<and> bit w 6 \<and> \<not> bit w 5
      then case ws of
        [] \<Rightarrow> RETURN (ws, None)
      | w' # ws' \<Rightarrow>
        if bit w' 7 \<and> \<not> bit w' 6 \<and> 127 < two_byte_codepoint w w'
        then RETURN (ws', Some (rs @ [two_byte_codepoint w w']))
        else RETURN (ws, None)
      else if bit w 7 \<and> bit w 6 \<and> bit w 5 \<and> \<not> bit w 4
      then case ws of
        [] \<Rightarrow> RETURN (ws, None)
      | [w'] \<Rightarrow> RETURN (ws, None)
      | w' # w'' # ws' \<Rightarrow>
        if bit w' 7 \<and> \<not> bit w' 6 \<and> bit w'' 7 \<and> \<not> bit w'' 6 \<and> 2047 < three_byte_codepoint w w' w''
        then RETURN (ws', Some (rs @ [three_byte_codepoint w w' w'']))
        else RETURN (ws, None)
      else if bit w 7 \<and> bit w 6 \<and> bit w 5 \<and> bit w 4 \<and> \<not> bit w 3
      then case ws of
        [] \<Rightarrow> RETURN (ws, None)
      | [w'] \<Rightarrow> RETURN (ws, None)
      | [w', w''] \<Rightarrow> RETURN (ws, None)
      | w' # w'' # w''' # ws' \<Rightarrow>
        if bit w' 7 \<and> \<not> bit w' 6 \<and> bit w'' 7 \<and> \<not> bit w'' 6 \<and> bit w''' 7 \<and> \<not> bit w''' 6 \<and>
           65535 < four_byte_codepoint w w' w'' w'''
        then RETURN (ws', Some (rs @ [four_byte_codepoint w w' w'' w''']))
        else RETURN (ws, None)
      else RETURN (ws, None))\<close>  

lemma decode_utf8_2_not_four_bytes_refines:
  assumes 
    \<open>length bs' + i = length bs\<close> and 
    conds: \<open>cond_decode_utf8_2 (length bs) (i, Some rs)\<close> \<open>cond_decode_utf8 (bs', Some rs)\<close> and 
    invars: \<open>invar_decode_utf8_2 (length bs) bs (i, Some rs)\<close> \<open>invar_decode_utf8 bs (bs', Some rs)\<close> and
    \<open>length bs \<le> i \<or> \<not> is_one_byte (bs ! i)\<close> and 
    \<open>\<not> is_continuation_byte (bs ! Suc i) \<or> \<not> bit (bs ! i) 6 \<or> \<not> bit (bs ! i) 7 \<or> length bs \<le> Suc i \<or>
    bit (bs ! i) 5 \<or> \<not> 127 < two_byte_codepoint (bs ! i) (bs ! Suc i)\<close> and
    \<open>\<not> is_continuation_byte (bs ! Suc (Suc i)) \<or> \<not> is_continuation_byte (bs ! Suc i) \<or>
    \<not> bit (bs ! i) 5 \<or> \<not> bit (bs ! i) 6 \<or> \<not> bit (bs ! i) 7 \<or> length bs \<le> Suc (Suc i) \<or>
    bit (bs ! i) 4 \<or> \<not> 2047 < three_byte_codepoint (bs ! i) (bs ! Suc i) (bs ! Suc (Suc i))\<close> and
    \<open>\<not> is_continuation_byte (bs ! Suc (Suc (Suc i))) \<or> \<not> is_continuation_byte (bs ! Suc (Suc i)) \<or>
    \<not> is_continuation_byte (bs ! Suc i) \<or> \<not> bit (bs ! i) 4 \<or> \<not> bit (bs ! i) 5 \<or> \<not> bit (bs ! i) 6 \<or> 
    \<not> bit (bs ! i) 7 \<or> length bs \<le> Suc (Suc (Suc i)) \<or> bit (bs ! i) 3 \<or>
    \<not> 65535 < four_byte_codepoint (bs ! i) (bs ! Suc i) (bs ! Suc (Suc i)) (bs ! Suc (Suc (Suc i)))\<close> 
  shows
    \<open>RETURN (Suc i, None) \<le> \<Down> (st_refine' (length bs)) (decode_utf8_body bs' rs)\<close>
proof (cases \<open>length bs \<le> i\<close>) 
  case True
  then show ?thesis
    using cond_decode_utf8_2_def conds(1)
    by auto
next
  case f1: False

  have not_one_byte: \<open>\<not> is_one_byte (bs ! i)\<close>
    using assms(6) f1
    by blast 

  obtain w ws where
    bs'_is: \<open>bs' = w # ws\<close> and
    w_is: \<open>bs ! i = w\<close>
    using assms(1) f1 conds invars(2)
    unfolding cond_decode_utf8_def cond_decode_utf8_2_def invar_decode_utf8_def
    by auto (metis Cons_nth_drop_Suc diff_add_inverse linorder_not_less) 

  show ?thesis
  proof (cases \<open>length bs \<le> Suc i\<close>) 
    case True
    then have \<open>ws = []\<close>
      by (metis f1 One_nat_def add_right_cancel assms(1) impossible_Cons le_SucE length_ge_1_conv
          plus_1_eq_Suc bs'_is) 
    then show ?thesis
      (* No matter what last the byte is, since it does not start with \<^verbatim>\<open>0\<close> then every sequence is
       * UTF-8 invalid. *)
      using not_one_byte assms(1) bs'_is w_is
      by auto
  next
    case f2: False

    have not_two_bytes:
      \<open>\<not> is_continuation_byte (bs ! Suc i) \<or> \<not> bit (bs ! i) 6 \<or> \<not> bit (bs ! i) 7 \<or> 
      bit (bs ! i) 5 \<or> \<not> 127 < two_byte_codepoint (bs ! i) (bs ! Suc i)\<close>
      using f2 assms(7)
      by blast 

    obtain w' ws' where
      ws_is: \<open>ws = w' # ws'\<close> and
      w'_is: \<open>bs ! Suc i = w'\<close>
      using assms(1) f2 conds invars(2)
      unfolding cond_decode_utf8_def cond_decode_utf8_2_def invar_decode_utf8_def
      by auto (metis Cons_nth_drop_Suc bs'_is diff_add_inverse leI le_Suc_eq list_tail_coinc) 

    show ?thesis
    proof (cases \<open>length bs \<le> Suc (Suc i)\<close>) 
      case True
      then have \<open>ws' = []\<close>
        using assms(1) bs'_is le_Suc_eq ws_is
        by auto
      then show ?thesis
        (* There are only two bytes left. The first one does not start with \<^verbatim>\<open>0\<close> nor \<^verbatim>\<open>110\<close>.
         * Hence any sequence of two bytes is UTF-8 invalid. *)
        using not_one_byte not_two_bytes f2 True bs'_is is_cont_iff_not_one w'_is w_is ws_is
        by auto
    next
      case f3: False

      have not_three_bytes:
        \<open>\<not> is_continuation_byte (bs ! Suc (Suc i)) \<or> \<not> is_continuation_byte (bs ! Suc i) \<or>
        \<not> bit (bs ! i) 5 \<or> \<not> bit (bs ! i) 6 \<or> \<not> bit (bs ! i) 7 \<or> bit (bs ! i) 4 \<or>
        \<not> 2047 < three_byte_codepoint (bs ! i) (bs ! Suc i) (bs ! Suc (Suc i))\<close>
        using f3 assms(8)
        by blast 

      obtain w'' ws'' where
        ws'_is: \<open>ws' = w'' # ws''\<close> and
        w''_is: \<open>bs ! Suc (Suc i) = w''\<close>
        using assms(1) f3 conds invars(2)
        unfolding cond_decode_utf8_def cond_decode_utf8_2_def invar_decode_utf8_def
        by auto (metis Cons_nth_drop_Suc bs'_is diff_add_inverse f1 f2 linorder_not_less list.inject
            ws_is) 

      show ?thesis
      proof (cases \<open>length bs \<le> Suc (Suc (Suc i))\<close>) 
        case True
        then have \<open>ws'' = []\<close>
          by (metis Suc3_eq_add_3 add_diff_cancel_right' assms(1) bs'_is diff_Suc_1 f3
              impossible_Cons le_SucE length_Cons length_ge_1_conv numerals_3 ws'_is ws_is) 
        then show ?thesis
          (* There are only three bytes left. Since the first one does not start with \<^verbatim>\<open>0\<close> nor \<^verbatim>\<open>110\<close>
           * nor \<^verbatim>\<open>1110\<close>, any sequence of three bytes is UTF-8 invalid. *)
          using not_one_byte not_two_bytes not_three_bytes True is_cont_iff_not_one f3
          using bs'_is w_is ws'_is w''_is w'_is RETURN_refine_iff
          (* A bit slow *)
          by (smt (verit) One_nat_def Suc_1 add_2_eq_Suc le_Suc_eq length_Cons list.simps(4)
              list.simps(5) list.size(3) mem_Collect_eq ws_is) 
      next
        case f4: False

        have not_four_bytes:
          \<open>\<not> is_continuation_byte (bs ! Suc (Suc (Suc i))) \<or>
          \<not> is_continuation_byte (bs ! Suc (Suc i)) \<or>
          \<not> is_continuation_byte (bs ! Suc i) \<or> \<not> bit (bs ! i) 4 \<or> \<not> bit (bs ! i) 5 \<or>
          \<not> bit (bs ! i) 6 \<or> \<not> bit (bs ! i) 7 \<or> bit (bs ! i) 3 \<or>
          \<not> 65535 < four_byte_codepoint (bs ! i) (bs ! Suc i) (bs ! Suc (Suc i)) (bs ! Suc (Suc (Suc i)))\<close>
          using f4 assms(9)
          by blast 

        obtain w''' ws''' where
          ws''_is: \<open>ws'' = w''' # ws'''\<close> and
          w'''_is: \<open>bs ! Suc (Suc (Suc i)) = w'''\<close>
          using assms(1) f4 conds invars(2)
          unfolding cond_decode_utf8_def cond_decode_utf8_2_def invar_decode_utf8_def
          apply auto
          by (metis Cons_nth_drop_Suc bs'_is diff_add_inverse f1 f2 f3 linorder_not_less list.inject
              ws'_is ws_is) 

        show ?thesis
          using not_one_byte not_two_bytes not_three_bytes not_four_bytes
          apply (elim disjE)
          unfolding is_continuation_byte_def
          using bs'_is w_is ws_is w'_is ws'_is w''_is ws''_is w'''_is assms(1)
          by auto
      qed
    qed
  qed
qed

lemma decode_utf8_2_four_bytes_refines:
  assumes 
    \<open>length bs' + i = length bs\<close> and 
    conds: \<open>cond_decode_utf8_2 (length bs) (i, Some rs)\<close> \<open>cond_decode_utf8 (bs', Some rs)\<close> and 
    invars: \<open>invar_decode_utf8_2 (length bs) bs (i, Some rs)\<close> \<open>invar_decode_utf8 bs (bs', Some rs)\<close> and
    \<open>Suc (Suc (Suc i)) < length bs\<close> and 
    \<open>bit (bs ! i) 7\<close> and 
    \<open>bit (bs ! i) 6\<close> and 
    \<open>bit (bs ! i) 5\<close> and
    \<open>bit (bs ! i) 4\<close> and
    \<open>\<not> bit (bs ! i) 3\<close> and 
    \<open>is_continuation_byte (bs ! Suc i)\<close> and
    \<open>is_continuation_byte (bs ! Suc (Suc i))\<close> and
    \<open>is_continuation_byte (bs ! Suc (Suc (Suc i)))\<close> and 
    \<open>65535 < four_byte_codepoint (bs ! i) (bs ! Suc i) (bs ! Suc (Suc i)) (bs ! Suc (Suc (Suc i)))\<close> and 
    \<open>cp = four_byte_codepoint (bs ! i) (bs ! Suc i) (bs ! Suc (Suc i)) (bs ! Suc (Suc (Suc i)))\<close> and 
    \<open>i' = i + 4\<close> 
  shows
    \<open>RETURN (i', Some (rs @ [cp])) \<le> \<Down> (st_refine' (length bs)) (decode_utf8_body bs' rs)\<close>
proof -
  obtain w w' w'' w''' ws where
    \<open>bs' = w # w' # w'' # w''' # ws\<close> and
    \<open>bs ! i = w\<close> and
    \<open>bs ! Suc i = w'\<close> and
    \<open>bs ! Suc (Suc i) = w''\<close> and
    \<open>bs ! Suc (Suc (Suc i)) = w'''\<close>
    using assms(1, 6) conds invars(2)
    unfolding cond_decode_utf8_2_def cond_decode_utf8_def invar_decode_utf8_def
    by (auto) (metis Cons_nth_drop_Suc Suc_lessD diff_add_inverse) 
  then show ?thesis
    using assms(1, 6-17) numerals_4
    unfolding is_continuation_byte_def
    by (auto, fastforce simp: assms(10))
    (* Uh, that's weird. *)
qed

lemma decode_utf8_2_not_three_bytes_refines:
  assumes 
    \<open>length bs' + i = length bs\<close> and 
    conds: \<open>cond_decode_utf8_2 (length bs) (i, Some rs)\<close> \<open>cond_decode_utf8 (bs', Some rs)\<close> and 
    invars: \<open>invar_decode_utf8_2 (length bs) bs (i, Some rs)\<close> \<open>invar_decode_utf8 bs (bs', Some rs)\<close> and
    \<open>length bs \<le> i \<or> \<not> is_one_byte (bs ! i)\<close> and 
    \<open>\<not> is_continuation_byte (bs ! Suc i) \<or> \<not> bit (bs ! i) 6 \<or> \<not> bit (bs ! i) 7 \<or> length bs \<le> Suc i \<or>
    bit (bs ! i) 5 \<or> \<not> 127 < two_byte_codepoint (bs ! i) (bs ! Suc i)\<close> and
    \<open>\<not> is_continuation_byte (bs ! Suc (Suc i)) \<or> \<not> is_continuation_byte (bs ! Suc i) \<or>
    \<not> bit (bs ! i) 5 \<or> \<not> bit (bs ! i) 6 \<or> \<not> bit (bs ! i) 7 \<or> length bs \<le> Suc (Suc i) \<or>
    bit (bs ! i) 4 \<or> \<not> 2047 < three_byte_codepoint (bs ! i) (bs ! Suc i) (bs ! Suc (Suc i))\<close> 
  shows
    \<open>do {
      (ia, y) \<leftarrow> decode_four_bytes bs i;
      case_option (RETURN (Suc i, None)) (\<lambda> cp. RETURN (ia, Some (rs @ [cp]))) y
    } \<le> \<Down> (st_refine' (length bs)) (decode_utf8_body bs' rs)\<close>
  apply (rule specify_left[OF decode_four_bytes_correct], refine_rcg, auto) 
  using decode_utf8_2_four_bytes_refines[OF assms(1-5)] decode_utf8_2_not_four_bytes_refines[OF assms]
  by (smt (z3) case_optionE option.simps(4) option.simps(5)) 

lemma decode_utf8_2_three_bytes_refines:
  assumes 
    \<open>length bs' + i = length bs\<close> and 
    conds: \<open>cond_decode_utf8_2 (length bs) (i, Some rs)\<close> \<open>cond_decode_utf8 (bs', Some rs)\<close> and 
    invars: \<open>invar_decode_utf8_2 (length bs) bs (i, Some rs)\<close> \<open>invar_decode_utf8 bs (bs', Some rs)\<close> and
    \<open>Suc (Suc i) < length bs\<close> and 
    \<open>bit (bs ! i) 7\<close> and 
    \<open>bit (bs ! i) 6\<close> and 
    \<open>bit (bs ! i) 5\<close> and 
    \<open>\<not> bit (bs ! i) 4\<close> and 
    \<open>is_continuation_byte (bs ! Suc i)\<close> and 
    \<open>is_continuation_byte (bs ! Suc (Suc i))\<close> and 
    \<open>2047 < three_byte_codepoint (bs ! i) (bs ! Suc i) (bs ! Suc (Suc i))\<close> and 
    \<open>cp = three_byte_codepoint (bs ! i) (bs ! Suc i) (bs ! Suc (Suc i))\<close> and 
    \<open>i' = i + 3\<close>
  shows
    \<open>RETURN (i', Some (rs @ [cp])) \<le> \<Down> (st_refine' (length bs)) (decode_utf8_body bs' rs)\<close>  
proof -
  obtain w w' w'' ws where
    \<open>bs' = w # w' # w'' # ws\<close> and
    \<open>bs ! i = w\<close> and
    \<open>bs ! Suc i = w'\<close> and
    \<open>bs ! Suc (Suc i) = w''\<close>
    using assms(1, 6) conds invars(2)
    unfolding cond_decode_utf8_def cond_decode_utf8_2_def invar_decode_utf8_def
    by (auto, metis Cons_nth_drop_Suc Suc_lessD diff_add_inverse) 
  then show ?thesis
    using assms(1, 6-15) numerals_3
    unfolding is_continuation_byte_def
    by auto 
qed

lemma decode_utf8_2_not_two_bytes_refines:
  assumes 
    \<open>length bs' + i = length bs\<close> and 
    conds: \<open>cond_decode_utf8_2 (length bs) (i, Some rs)\<close> \<open>cond_decode_utf8 (bs', Some rs)\<close> and 
    invars: \<open>invar_decode_utf8_2 (length bs) bs (i, Some rs)\<close> \<open>invar_decode_utf8 bs (bs', Some rs)\<close> and
    \<open>length bs \<le> i \<or> \<not> is_one_byte (bs ! i)\<close> and 
    \<open>\<not> is_continuation_byte (bs ! Suc i) \<or> \<not> bit (bs ! i) 6 \<or> \<not> bit (bs ! i) 7 \<or> length bs \<le> Suc i \<or>
    bit (bs ! i) 5 \<or> \<not> 127 < two_byte_codepoint (bs ! i) (bs ! Suc i)\<close> 
  shows
    \<open>do {
      (ia, y) \<leftarrow> decode_three_bytes bs i;
      case_option (do {
        (ia, y) \<leftarrow> decode_four_bytes bs i;
        case_option (RETURN (Suc i, None)) (\<lambda> cp. RETURN (ia, Some (rs @ [cp]))) y
      }) (\<lambda> cp. RETURN (ia, Some (rs @ [cp]))) y
    } \<le> \<Down> (st_refine' (length bs)) (decode_utf8_body bs' rs)\<close>
  apply (rule specify_left[OF decode_three_bytes_correct], refine_rcg, auto)
  using decode_utf8_2_three_bytes_refines[OF assms(1-5)] decode_utf8_2_not_three_bytes_refines[OF assms]
  by (smt (z3) case_optionE option.simps(4) option.simps(5)) 

lemma decode_utf8_2_two_bytes_refines:
  assumes
    \<open>length bs' + i = length bs\<close> and 
    conds: \<open>cond_decode_utf8_2 (length bs) (i, Some rs)\<close> \<open>cond_decode_utf8 (bs', Some rs)\<close> and 
    invars: \<open>invar_decode_utf8_2 (length bs) bs (i, Some rs)\<close> \<open>invar_decode_utf8 bs (bs', Some rs)\<close> and
    \<open>Suc i < length bs\<close> and 
    \<open>bit (bs ! i) 7\<close> and 
    \<open>bit (bs ! i) 6\<close> and
    \<open>\<not> bit (bs ! i) 5\<close> and
    \<open>is_continuation_byte (bs ! Suc i)\<close> and 
    \<open>127 < two_byte_codepoint (bs ! i) (bs ! Suc i)\<close> and 
    \<open>cp = two_byte_codepoint (bs ! i) (bs ! Suc i)\<close> and 
    \<open>i' = Suc (Suc i)\<close> 
  shows
    \<open>RETURN (i', Some (rs @ [cp])) \<le> \<Down> (st_refine' (length bs)) (decode_utf8_body bs' rs)\<close>
proof -
  obtain w w' ws where
    \<open>bs' = w # w' # ws\<close> and
    \<open>bs ! i = w\<close> and
    \<open>bs ! Suc i = w'\<close>
    using assms(1, 6) conds invars(2)
    unfolding cond_decode_utf8_def cond_decode_utf8_2_def invar_decode_utf8_def
    by (auto, metis Cons_nth_drop_Suc diff_add_inverse drop_eq_Nil linorder_not_less)
  then show ?thesis
    using assms(1, 6-13)
    unfolding is_continuation_byte_def
    by auto 
qed

lemma decode_utf8_2_not_one_byte_refines:
  assumes 
    \<open>length bs' + i = length bs\<close> and 
    conds: \<open>cond_decode_utf8_2 (length bs) (i, Some rs)\<close> \<open>cond_decode_utf8 (bs', Some rs)\<close> and 
    invars: \<open>invar_decode_utf8_2 (length bs) bs (i, Some rs)\<close> \<open>invar_decode_utf8 bs (bs', Some rs)\<close> and
    \<open>length bs \<le> i \<or> \<not> is_one_byte (bs ! i)\<close>  
  shows
    \<open>do {
      (ia, y) \<leftarrow> decode_two_bytes bs i;
      case_option (do {
        (ia, y) \<leftarrow> decode_three_bytes bs i;
        case_option (do {
          (ia, y) \<leftarrow> decode_four_bytes bs i;
          case_option (RETURN (Suc i, None)) (\<lambda> cp. RETURN (ia, Some (rs @ [cp]))) y
        }) (\<lambda> cp. RETURN (ia, Some (rs @ [cp]))) y
      }) (\<lambda> cp. RETURN (ia, Some (rs @ [cp]))) y
    } \<le> \<Down> (st_refine' (length bs)) (decode_utf8_body bs' rs)\<close>
  apply (rule specify_left[OF decode_two_bytes_correct], refine_rcg, auto)
  using decode_utf8_2_two_bytes_refines[OF assms(1-5)] decode_utf8_2_not_two_bytes_refines[OF assms]
  by (smt (z3) case_optionE option.simps(4) option.simps(5)) 

lemma decode_utf8_2_one_byte_refines:
  assumes
    \<open>length bs' + i = length bs\<close> and 
    conds: \<open>cond_decode_utf8_2 (length bs) (i, Some rs)\<close> \<open>cond_decode_utf8 (bs', Some rs)\<close> and 
    invars: \<open>invar_decode_utf8_2 (length bs) bs (i, Some rs)\<close> \<open>invar_decode_utf8 bs (bs', Some rs)\<close> and
    \<open>i < length bs\<close> and
    \<open>is_one_byte (bs ! i)\<close> and
    \<open>cp = word8_to_word24 (take_bit 6 (bs ! i))\<close> and
    \<open>i' = i + 1\<close> 
  shows
    \<open>RETURN (i', Some (rs @ [cp])) \<le> \<Down> (st_refine' (length bs)) (decode_utf8_body bs' rs)\<close>
proof -  
  obtain w ws where
    \<open>bs' = w # ws\<close> and
    \<open>bs ! i = w\<close>
    using assms(1, 6) conds invars(2)
    unfolding cond_decode_utf8_def cond_decode_utf8_2_def invar_decode_utf8_def
    by (auto, metis Cons_nth_drop_Suc diff_add_inverse)
  then show ?thesis
    using assms(1, 6-9)
    by simp 
qed

lemma decode_utf8_2_body_refines:
  assumes
    \<open>length bs' + i = length bs\<close> and 
    conds: \<open>cond_decode_utf8_2 (length bs) (i, Some rs)\<close> \<open>cond_decode_utf8 (bs', Some rs)\<close> and 
    invars: \<open>invar_decode_utf8_2 (length bs) bs (i, Some rs)\<close> \<open>invar_decode_utf8 bs (bs', Some rs)\<close> 
  shows 
    \<open>do {
      (ia, y) \<leftarrow> decode_one_byte bs i;
      case_option (do {
        (ia, y) \<leftarrow> decode_two_bytes bs i;
        case_option (do {
          (ia, y) \<leftarrow> decode_three_bytes bs i;
          case_option (do {
            (ia, y) \<leftarrow> decode_four_bytes bs i;
            case_option (RETURN (Suc i, None)) (\<lambda> cp. RETURN (ia, Some (rs @ [cp]))) y
          }) (\<lambda> cp. RETURN (ia, Some (rs @ [cp]))) y
        }) (\<lambda> cp. RETURN (ia, Some (rs @ [cp]))) y
      }) (\<lambda> cp. RETURN (ia, Some (rs @ [cp]))) y
    } \<le> \<Down> (st_refine' (length bs)) (decode_utf8_body bs' rs)\<close>
  apply (rule specify_left[OF decode_one_byte_correct], refine_rcg, auto) 
  using decode_utf8_2_not_one_byte_refines[OF assms] decode_utf8_2_one_byte_refines[OF assms] 
  by (smt (z3) Suc_eq_plus1 case_optionE option.simps(4) option.simps(5))  

theorem decode_utf8_2_correct: \<open>decode_utf8_2 bs \<le> \<Down> (\<langle>Id\<rangle>option_rel) (decode_utf8 bs)\<close>
  unfolding decode_utf8_def decode_utf8_2_def
  by (refine_rcg WHILEIT_refine[where R=\<open>st_refine (length bs)\<close>] case_option_refine[where Ra=\<open>Id\<close>],
    auto simp add: invar_decode_utf8_2_if cond_decode_utf8_iff_cond_decode_utf8_2
      decode_utf8_2_body_refines)

section \<open>Simplified UTF-8 parser\<close>

definition decode_one_byte_2 :: \<open>byte_string \<Rightarrow> nat \<Rightarrow> (nat \<times> uint32 option) nres\<close> where
  \<open>decode_one_byte_2 bs i \<equiv>
    if length bs \<le> i
    then RETURN (i + 1, None)
    else if bit (bs ! i) 7
    then RETURN (i + 1, None)
    else RETURN (i + 1, Some (word8_to_word24 (take_bit 6 (bs ! i))))\<close>

definition decode_two_bytes_2 :: \<open>byte_string \<Rightarrow> nat \<Rightarrow> (nat \<times> uint32 option) nres\<close> where
  \<open>decode_two_bytes_2 bs i \<equiv>
    if length bs \<le> i + 1
    then RETURN (i + 1, None)
    else if \<not> bit (bs ! i) 7
    then RETURN (i + 1, None)
    else if \<not> bit (bs ! i) 6
    then RETURN (i + 1, None)
    else if bit (bs ! i) 5
    then RETURN (i + 1, None)
    else if \<not> bit (bs ! (i + 1)) 7
    then RETURN (i + 1, None)
    else if bit (bs ! (i + 1)) 6
    then RETURN (i + 1, None)
    else if two_byte_codepoint (bs ! i) (bs ! (i + 1)) \<le> 0x7F
    then RETURN (i + 1, None)
    else RETURN (i + 2, Some (two_byte_codepoint (bs ! i) (bs ! (i + 1))))\<close> 

definition decode_three_bytes_2 :: \<open>byte_string \<Rightarrow> nat \<Rightarrow> (nat \<times> uint32 option) nres\<close> where
  \<open>decode_three_bytes_2 bs i \<equiv>
    if length bs \<le> i + 2
    then RETURN (i + 1, None)
    else if \<not> bit (bs ! i) 7
    then RETURN (i + 1, None)
    else if \<not> bit (bs ! i) 6
    then RETURN (i + 1, None)
    else if \<not> bit (bs ! i) 5
    then RETURN (i + 1, None)
    else if bit (bs ! i) 4
    then RETURN (i + 1, None)
    else if \<not> bit (bs ! (i + 1)) 7
    then RETURN (i + 1, None)
    else if bit (bs ! (i + 1)) 6
    then RETURN (i + 1, None)
    else if \<not> bit (bs ! (i + 2)) 7
    then RETURN (i + 1, None)
    else if bit (bs ! (i + 2)) 6
    then RETURN (i + 1, None)
    else if three_byte_codepoint (bs ! i) (bs ! (i + 1)) (bs ! (i + 2)) \<le> 0x7FF
    then RETURN (i + 1, None)
    else RETURN (i + 3, Some (three_byte_codepoint (bs ! i) (bs ! (i + 1)) (bs ! (i + 2))))\<close> 

definition decode_four_bytes_2 :: \<open>byte_string \<Rightarrow> nat \<Rightarrow> (nat \<times> uint32 option) nres\<close> where
  \<open>decode_four_bytes_2 bs i \<equiv>
    if length bs \<le> i + 3
    then RETURN (i + 1, None)
    else if \<not> bit (bs ! i) 7
    then RETURN (i + 1, None)
    else if \<not> bit (bs ! i) 6
    then RETURN (i + 1, None)
    else if \<not> bit (bs ! i) 5
    then RETURN (i + 1, None)
    else if \<not> bit (bs ! i) 4
    then RETURN (i + 1, None)
    else if bit (bs ! i) 3
    then RETURN (i + 1, None)
    else if \<not> bit (bs ! (i + 1)) 7
    then RETURN (i + 1, None)
    else if bit (bs ! (i + 1)) 6
    then RETURN (i + 1, None)
    else if \<not> bit (bs ! (i + 2)) 7
    then RETURN (i + 1, None)
    else if bit (bs ! (i + 2)) 6
    then RETURN (i + 1, None)
    else if \<not> bit (bs ! (i + 3)) 7
    then RETURN (i + 1, None)
    else if bit (bs ! (i + 3)) 6
    then RETURN (i + 1, None)
    else if four_byte_codepoint (bs ! i) (bs ! (i + 1)) (bs ! (i + 2)) (bs ! (i + 3)) \<le> 0xFFFF
    then RETURN (i + 1, None)
    else RETURN (i + 4, Some (four_byte_codepoint (bs ! i) (bs ! (i + 1)) (bs ! (i + 2)) (bs ! (i + 3))))\<close> 

lemma plus_one_is_Suc: \<open>x + 1 = Suc x\<close>
  by simp

lemma plus_two_is_Suc_Suc: \<open>x + 2 = Suc (Suc x)\<close>
  by simp

lemma plus_three_is_Suc_Suc_Suc: \<open>x + 3 = Suc (Suc (Suc x))\<close>
  by simp 

lemma decode_one_byte_2_refines: \<open>decode_one_byte_2 bs i \<le> \<Down> Id (decode_one_byte bs i)\<close>
  unfolding decode_one_byte_2_def decode_one_byte_def
  apply (rewrite Transfer.if_conn(2)) 
  by refine_rcg

lemma decode_two_bytes_2_refines: \<open>decode_two_bytes_2 bs i \<le> \<Down> Id (decode_two_bytes bs i)\<close>
  unfolding decode_two_bytes_2_def decode_two_bytes_def
  apply (rewrite Transfer.if_conn(2) plus_one_is_Suc)+
  by refine_rcg

lemma decode_three_bytes_2_refines: \<open>decode_three_bytes_2 bs i \<le> \<Down> Id (decode_three_bytes bs i)\<close> 
  unfolding decode_three_bytes_2_def decode_three_bytes_def
  apply (rewrite Transfer.if_conn(2) plus_one_is_Suc plus_two_is_Suc_Suc)+
  by refine_rcg

lemma decode_four_bytes_2_refines: \<open>decode_four_bytes_2 bs i \<le> \<Down> Id (decode_four_bytes bs i)\<close>
  unfolding decode_four_bytes_2_def decode_four_bytes_def
  apply (rewrite Transfer.if_conn(2) plus_one_is_Suc plus_two_is_Suc_Suc plus_three_is_Suc_Suc_Suc)+
  by refine_rcg

definition decode_utf8_3 :: \<open>byte_string \<Rightarrow> codepoint_string option nres\<close> where
  \<open>decode_utf8_3 bs \<equiv> do {
    (_, st) \<leftarrow> WHILE\<^sub>T\<^bsup>invar_decode_utf8_2 (length bs) bs\<^esup> (cond_decode_utf8_2 (length bs)) (\<lambda> (i, st). case st of
      None \<Rightarrow> RETURN (i, None)
    | Some ws \<Rightarrow> do {
      res \<leftarrow> decode_one_byte_2 bs i;
      case res of
        (i, Some cp) \<Rightarrow> RETURN (i, Some (ws @ [cp]))
      | (_, None) \<Rightarrow> do {
        res \<leftarrow> decode_two_bytes_2 bs i;
        case res of
          (i, Some cp) \<Rightarrow> RETURN (i, Some (ws @ [cp]))
        | (_, None) \<Rightarrow> do {
          res \<leftarrow> decode_three_bytes_2 bs i;
          case res of
            (i, Some cp) \<Rightarrow> RETURN (i, Some (ws @ [cp]))
          | (_, None) \<Rightarrow> do {
            res \<leftarrow> decode_four_bytes_2 bs i;
            case res of
              (i, Some cp) \<Rightarrow> RETURN (i, Some (ws @ [cp]))
            | (_, None) \<Rightarrow> RETURN (i + 1, None)
          }
        }
      }
    }) (0, Some []);
    RETURN st
  }\<close>

theorem decode_utf8_3_refines: \<open>decode_utf8_3 bs \<le> \<Down> (\<langle>Id\<rangle>option_rel) (decode_utf8_2 bs)\<close>
  unfolding decode_utf8_3_def decode_utf8_2_def
  apply (refine_rcg WHILEIT_refine[where R=\<open>st_refine (length bs)\<close>]) 
  (* Why isn't \<open>?R\<close> instantiated????????? *)
  sorry
  
  


section \<open>Array-based UTF-8 parser\<close>

text \<open>
  @{const decode_utf8_3} is a correct executable UTF-8 parser.
  However, it uses lists and direct indexing, which are very slow (direct indexing takes $O(n)$ in
  linked lists).
  We refine this decoder to use finite arrays instead of linked lists to obtain a more efficient
  algorithm.
\<close> 

instance uint8 :: countable
proof standard
  have \<open>inj nat_of_uint8\<close>
    by (metis Abs_uint8_cases Abs_uint8_inverse inj_def nat_of_uint8.rep_eq unsigned_word_eqI) 
  then show \<open>\<exists> to_nat :: uint8 \<Rightarrow> nat. inj to_nat\<close>
    by blast 
qed 

instance uint8 :: heap .. 

instance uint32 :: countable
proof standard
  have \<open>inj nat_of_uint32\<close>
    by (metis (mono_tags, lifting) Quotient_rel_abs2 Quotient_uint32 inj_def nat_of_uint32.rep_eq
        unsigned_word_eqI)
  then show \<open>\<exists> to_nat :: uint32 \<Rightarrow> nat. inj to_nat\<close>
    by blast
qed

instance uint32 :: heap .. 

sepref_definition w8_to_w32_impl is \<open>RETURN \<circ> word8_to_word24\<close>
  :: \<open>id_assn\<^sup>k \<rightarrow>\<^sub>a id_assn\<close>
  unfolding word8_to_word24_def


  apply sepref_dbg_preproc
  apply sepref_dbg_cons_init
  apply sepref_dbg_id
  apply sepref_dbg_opt_init
  apply sepref_dbg_monadify 

  apply sepref_dbg_trans_step+

  apply sepref_dbg_opt 

sepref_definition decode_one_byte_2_impl is \<open>uncurry decode_one_byte_2\<close>
  :: \<open>(arl_assn id_assn)\<^sup>k *\<^sub>a id_assn\<^sup>k \<rightarrow>\<^sub>a prod_assn id_assn (option_assn id_assn)\<close>
  unfolding decode_one_byte_2_def word8_to_word24_def 
  (* I don't understand why the SEPREF tool struggles with this. *)
   
  
  sorry



sepref_definition decode_two_bytes_impl is \<open>uncurry (PR_CONST decode_two_bytes)\<close>
  :: \<open>(arl_assn word8_assn)\<^sup>k *\<^sub>a id_assn\<^sup>k \<rightarrow>\<^sub>a prod_assn id_assn (option_assn word24_assn)\<close>
  sorry

sepref_definition decode_three_bytes_impl is \<open>uncurry (PR_CONST decode_three_bytes)\<close>
  :: \<open>(arl_assn word8_assn)\<^sup>k *\<^sub>a id_assn\<^sup>k \<rightarrow>\<^sub>a prod_assn id_assn (option_assn word24_assn)\<close>
  sorry

sepref_definition decode_four_bytes_impl is \<open>uncurry (PR_CONST decode_four_bytes)\<close>
  :: \<open>(arl_assn word8_assn)\<^sup>k *\<^sub>a id_assn\<^sup>k \<rightarrow>\<^sub>a prod_assn id_assn (option_assn word24_assn)\<close>
  sorry

sepref_definition decode_utf8_impl is \<open>PR_CONST decode_utf8_2\<close>
  :: \<open>(array_assn word8_assn)\<^sup>d \<rightarrow>\<^sub>a option_assn (arl_assn word24_assn)\<close>
  unfolding decode_utf8_2_def
   
  (* by sepref *)  
  sorry 

(* definition decode_codepoint :: \<open>char array \<Rightarrow> nat \<Rightarrow> (nat \<times> cp option) Heap\<close> where
  \<open>decode_codepoint bs i \<equiv> undefined\<close> 
 
definition decode_utf8_impl :: \<open>char array \<Rightarrow> cp array option Heap\<close> where
  \<open>decode_utf8_3 bs \<equiv> do {
    lim \<leftarrow> Array.len bs;
    cs \<leftarrow> arl_empty;
    (cs, _) \<leftarrow> heap.fixp_fun (\<lambda> rec (i, j, cs).
      case cs of
        None \<Rightarrow> return None
      | Some cs \<Rightarrow>
        if i \<ge> lim
        then return (Some cs)
        else do { 
          (i, w) \<leftarrow> decode_codepoint bs i;
          case w of
            None \<Rightarrow> return None
          | Some w \<Rightarrow> do { 
            i \<leftarrow> assert ((\<ge>) lim) i;
            k \<leftarrow> Array.len cs;
            cs \<leftarrow> if j = k then array_grow cs (k * 2) 0 else return cs;
            cs \<leftarrow> Array.upd j w cs;
            rec (i, Suc i, cs)
          }
        }
    ) (0, 0, Some cs);
    return cs
  }\<close> 

theorem decode_utf8_3_correct:
  shows
    \<open>hn_refine (array_assn word8_assn bs bs') (decode_utf8_3 bs') emp
      (option_assn (arl_assn word24_assn)) (decode_utf8_2 bs)\<close>
  sorry

text \<open>
  Finally, we export the concrete implementation to Haskell (because that's our main target).
\<close> 

export_code decode_utf8_3 checking Haskell
export_code decode_utf8_3 in Haskell *)

export_code decode_utf8_impl checking Haskell
export_code decode_utf8_impl in SML_imp

ML\<open>
  val arr : Word8.word array = Array.array (1, Word8.fromInt 0);

  @{code decode_utf8_impl} 
\<close> 

end (* theory Utf8Reader *)
