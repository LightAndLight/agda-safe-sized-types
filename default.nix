{ lib, agdaPackages }:
agdaPackages.mkDerivation {
  pname = "safe-sized-types";
  version = "0.0.1";

  src = lib.fileset.toSource {
    root = ./.;
    fileset = lib.fileset.unions [
      ./package.agda-lib
      ./src
    ];
  };

  libraryName = "safe-sized-types";
  libraryFile = "package.agda-lib";

  buildInputs = [ agdaPackages.standard-library ];

  meta = {
    description = "Sized types and coinduction in Safe Agda";
    homepage = "https://github.com/LightAndLight/agda-safe-sized-types";
  };
}

