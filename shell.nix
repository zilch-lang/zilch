{ pkgs ? import ./nix/nixpkgs-pinned.nix }:

pkgs.mkShell {
  name = "gzc-shell";
  version = "0.0.1";

  buildInputs = with pkgs; [
    stack
    (haskell-language-server.override {
      supportedGhcVersions = [ "8107" ];
    })

    haskellPackages.hoogle

    plantuml
  ];
}
