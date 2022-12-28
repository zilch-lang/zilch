#!/usr/bin/env bash

# Unfortunately I need this, because my Emacs installation seems a little bit broken for some reason.
# Sometimes, it is inserting raw Unicode symbols instead of Isabelle-syntax ones.
# This means that Isabelle is not able to compile the source code at all (but the LSP can?).
# So we simply perform substitution here, for most of the commonly used symbols.

# All taken from <https://github.com/NixOS/nixpkgs/blob/e4644a5b582703e6fa3b1c2e97a99e3bc3f7ce4c/pkgs/stdenv/generic/setup.sh#L370-L409>.
# Allows performing in-place string substitution in pure Bash.
substitute() {
    local input="$1"
    local output="$2"

    local -a params=("$@")

    local n p pattern replacement varName content

    # a slightly hacky way to keep newline at the end
    content="$(cat "$input"; printf "%s" X)"
    content="${content%X}"

    for ((n = 2; n < ${#params[*]}; n += 1)); do
        p=${params[$n]}

        if [ "$p" = --replace ]; then
            pattern="${params[$((n + 1))]}"
            replacement="${params[$((n + 2))]}"
            n=$((n + 2))
        fi

        if [ "$p" = --subst-var ]; then
            varName="${params[$((n + 1))]}"
            pattern="@$varName@"
            replacement="${!varName}"
            n=$((n + 1))
        fi

        if [ "$p" = --subst-var-by ]; then
            pattern="@${params[$((n + 1))]}@"
            replacement="${params[$((n + 2))]}"
            n=$((n + 2))
        fi

        content="${content//"$pattern"/$replacement}"
    done

    if [ -e "$output" ]; then chmod +w "$output"; fi
    printf "%s" "$content" > "$output"
}


substituteInPlace() {
    local fileName="$1"
    shift
    substitute "$fileName" "$fileName" "$@"
}

##################################################################################

substituteUnicodeInPlace() {
    echo "Patching file '$1'…"
    substituteInPlace "$1" \
        --replace "⇒" "\<Rightarrow>" \
        --replace "⇀" "\<rightharpoonup>" \
        --replace "×" "\<times>" \
        --replace "›" "\<close>" \
        --replace "‹" "\<open>" \
        --replace "←" "\<leftarrow>" \
        --replace "≡" "\<equiv>" \
        --replace "↦" "\<mapsto>" \
        --replace "λ" "\<lambda>" \
        --replace "⤜" "\<bind>" \
        --replace "⋀" "\<And>"
}

export -f substitute
export -f substituteInPlace
export -f substituteUnicodeInPlace

find src -name '*.thy' -exec bash -c 'substituteUnicodeInPlace "$@"' bash {} \;
find app -name '*.thy' -exec bash -c 'substituteUnicodeInPlace "$@"' bash {} \;
