{
  inputs = {
    flake-utils.url = "github:numtide/flake-utils";
    agda2hs.url = "github:agda/agda2hs";
  };
  outputs = { self, nixpkgs, flake-utils, agda2hs }:
    flake-utils.lib.eachDefaultSystem (system:
      let 
        pkgs = import nixpkgs { inherit system; };
      in {
        devShell = pkgs.mkShell {
          buildInputs = with pkgs; [
            (agda.withPackages (p: [ p.standard-library ]))
          ];
        };
      }
    );
}
