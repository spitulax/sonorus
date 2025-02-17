{ lib
, rustPlatform
, version ? "git"

, debug ? false
}:
rustPlatform.buildRustPackage ({
  pname = "sonorus";
  inherit version;
  src = lib.cleanSource ./..;

  cargoLock = {
    lockFile = ../Cargo.lock;
    allowBuiltinFetchGit = true;
  };

  meta = {
    description = "Advanced sound changer";
    mainProgram = "sonorus";
    homepage = "https://github.com/spitulax/sonorus";
    license = lib.licenses.mit;
    platforms = lib.platforms.all;
  };
} // (
  if debug then {
    buildType = "debug";
    dontStrip = true;
  }
  else { }
))
