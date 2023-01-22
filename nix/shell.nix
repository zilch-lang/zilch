{ pkgs ? import ./nixpkgs-pinned.nix }:

let
  ghc = pkgs.haskell.compiler.ghc90;
in
pkgs.mkShell {
  name = "gzc-shell";
  version = "0.0.1";

  buildInputs = with pkgs; [
    stack
    ghc
    (haskell-language-server.override {
      supportedGhcVersions = [ "902" ];
    })
    ed
    # For LiquidHaskell
    z3
    cvc4
  ];
}
