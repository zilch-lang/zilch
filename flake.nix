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

        isabelle-lib = isabelle2022.lib { inherit system pkgs isabelle; };

        haskellPackages = pkgs.haskell.packages.ghc8107.override {
          overrides = new: old:
            let
              diagnose' = pkgs.haskell.lib.enableCabalFlag old.diagnose "megaparsec-compat";
              diagnose = pkgs.haskell.lib.overrideCabal diagnose' (drv: {
                buildDepends = [ old.megaparsec ];
              });
            in
            {
              inherit diagnose;
            };
        };
        isabelle = isabelle2022.packages.${system}.isabelle.withComponents [
          isabelle2022.packages.${system}.isabelle-afp
        ];

        jailbreakUnbreak = pkg:
          pkgs.haskell.lib.doJailbreak (pkg.overrideAttrs (_: { meta = { }; }));

        gzcSource = isabelle-lib.export {
          session = "EntryPoint";
          src = self;
          texlive = pkgs.texlive.combined.scheme-full;
        };
        # Change this so that it generates the Haskell code before via Isabelle
        # Also add dependency to N* (nsc-core)
        gzc = haskellPackages.callCabal2nix "gzc"
          "${gzcSource.outPath}/build"
          {
            nsc-core = nstar.packages.${system}.nsc-core;
          };
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
            isabelle-lib.custom-emacs
          ];
          # inputsFrom = builtins.attrValues self.packages.${system};
        };
      }
    );
}

