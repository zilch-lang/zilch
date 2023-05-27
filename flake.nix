{
  description = "The Great Zilch Compiler";

  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs";
    flake-utils.url = "github:numtide/flake-utils";
    isabelle2022 = {
      url =
        # "git+file:///home/mesabloo/projects/isabelle.nix";
        "github:Mesabloo/isabelle.nix";
      inputs.flake-utils.follows = "flake-utils";
    };
    nstar = {
      url = "github:zilch-lang/nstar/develop";
      inputs.flake-utils.follows = "flake-utils";
    };
  };

  outputs = { self, nixpkgs, flake-utils, isabelle2022, nstar }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs { inherit system; };

        haskellPackages = pkgs.haskell.packages.ghc8107;
        isabelle = isabelle2022.packages.${system}.isabelle;

        jailbreakUnbreak = pkg:
          pkgs.haskell.lib.doJailbreak (pkg.overrideAttrs (_: { meta = { }; }));

        # Change this so that it generates the Haskell code before via Isabelle
        # Also add dependency to N* (nsc-core)
        gzc = pkgs.haskell.lib.overrideCabal
          (haskellPackages.callCabal2nix "gzc" self {
            # configurePhase = ''
            #   ${isabelle}/bin/isabelle build -v -d . -e EntryPoint
            # '';
            nsc-core = nstar.packages.${system}.nsc-core;
          })
          (drv: {
            preBuild = ''
              ${isabelle}/bin/isabelle build -d ${self} -e EntryPoint
            '' + (drv.preBuild or "");
          });
      in
      {
        packages = rec {
          inherit gzc;
        };

        apps = rec {
          gzc = flake-utils.lib.mkApp {
            drv = self.packages.${system}.gzc;
            name = "gzc";
          };
          default = gzc;
        };

        devShell = pkgs.mkShell {
          buildInputs = [
            haskellPackages.haskell-language-server
            haskellPackages.cabal-install
            isabelle
            isabelle2022.packages.${system}.emacs
          ];
          inputsFrom = builtins.attrValues self.packages.${system};
        };
      }
    );
}

