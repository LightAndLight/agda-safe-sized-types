{
  inputs = {
    flake-utils.url = "github:numtide/flake-utils";
  };
  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system:
      let 
        pkgs = import nixpkgs { inherit system; };
      in {
        devShell = pkgs.mkShell {
          buildInputs = with pkgs; [
            (agda.withPackages (p: [ p.standard-library ]))
          ];
        };
        packages.default = pkgs.agdaPackages.callPackage ./default.nix {};
      }
    );
}
