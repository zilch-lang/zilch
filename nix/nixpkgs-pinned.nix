import
  (builtins.fetchTarball {
    name = "nixpkgs-pinned";
    url = "https://github.com/nixos/nixpkgs/archive/ba6ba2b90096dc49f448aa4d4d783b5081b1cc87.tar.gz";
    # Use `nix-prefetch-url --unpack <url>`
    sha256 = "07asnnvp49wg419f7819iv7y8xhgxxzig1fjm72ii1g2mi3vmc1s";
  })
{ }

