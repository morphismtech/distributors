{
  description = "distributors, distributors-grammar & distributors-json";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = nixpkgs.legacyPackages.${system};
        lib = pkgs.haskell.lib;
        # nixpkgs' default GHC, whose packages are cached by cache.nixos.org
        haskellPackages = pkgs.haskellPackages.override {
          overrides = self: super: {
            distributors = self.callCabal2nix "distributors"
              ./distributors-core { };
            distributors-grammar = self.callCabal2nix "distributors-grammar"
              ./distributors-grammar { };
            distributors-json = self.callCabal2nix "distributors-json"
              ./distributors-json { };
          };
        };
      in
      {
        packages = {
          distributors = haskellPackages.distributors;
          distributors-grammar = haskellPackages.distributors-grammar;
          distributors-json = haskellPackages.distributors-json;
          default = haskellPackages.distributors-json;
        };

        checks = {
          distributors = lib.doBenchmark haskellPackages.distributors;
          distributors-grammar =
            lib.doBenchmark haskellPackages.distributors-grammar;
          distributors-json = lib.doBenchmark haskellPackages.distributors-json;
        };

        devShells.default = haskellPackages.shellFor {
          packages = p:
            [ p.distributors p.distributors-grammar p.distributors-json ];
          withHoogle = false;
          nativeBuildInputs = [
            pkgs.cabal-install
            pkgs.hlint
            pkgs.hpack
          ];
        };
      });
}
