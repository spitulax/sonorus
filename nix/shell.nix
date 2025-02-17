{ self
, pkgs
, mkShell
, rust-bin
}:
mkShell {
  name = "sonorus-shell";
  nativeBuildInputs = [
    rust-bin.latest.default
  ];
  inputsFrom = [
    self.packages.${pkgs.system}.default
  ];
}
