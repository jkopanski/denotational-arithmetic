{
  description = "Correct arithmetic by denotational design.";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs?ref=23.05";
    utils.url = "github:numtide/flake-utils";
    agda-stdlib = {
      url = "github:jkopanski/agda-stdlib";
      inputs = {
        nixpkgs.follows = "nixpkgs";
      };
    };
    felix = {
      url = "github:jkopanski/felix";
      inputs = {
        nixpkgs.follows = "nixpkgs";
        utils.follows = "utils";
        agda-stdlib.follows = "agda-stdlib";
      };
    };
    felix-boolean = {
      url = "github:jkopanski/felix-boolean";
      inputs = {
        nixpkgs.follows = "nixpkgs";
        utils.follows = "utils";
        agda-stdlib.follows = "agda-stdlib";
        felix.follows = "felix";
      };
    };
  };
  
  outputs = { self, nixpkgs, utils, agda-stdlib, felix, felix-boolean }:
    utils.lib.eachDefaultSystem (system:
      let
        pkgs = nixpkgs.legacyPackages.${system};
        standard-library = agda-stdlib.packages.${system}.default;
        felix-lib = felix.packages.${system}.default;
        felix-boolean-lib = felix-boolean.packages.${system}.default;
        agdaWithStandardLibrary = pkgs.agda.withPackages (p: [
          standard-library
          felix-lib
          felix-boolean-lib
          p.agda-categories
        ]);

      in {
        devShell = pkgs.mkShell {
          buildInputs = [
            agdaWithStandardLibrary
            pkgs.graphviz
          ];
        };

        packages.default = pkgs.agdaPackages.mkDerivation {
          pname = "felix-arithmetic";
          version = "0.0.1";
          src = ./.;

          buildInputs = [
            standard-library
            felix-lib
            felix-boolean-lib
            pkgs.agdaPackages.agda-categories
          ];

          meta = with pkgs.lib; {
            description = "Experiments of synthesis of correct hardware.";
            homepage = "https://git.sr.ht/~madnat/felix-arithmetic";
            license = licenses.agpl3;
            # platforms = platforms.unix;
            # maintainers = with maintainers; [ ];
          };
        };
      }
    );
}
