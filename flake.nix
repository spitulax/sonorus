{
  description = "Advanced sound changer";

  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs/nixos-unstable";
    rust-overlay = {
      url = "github:oxalica/rust-overlay";
      inputs.nixpkgs.follows = "nixpkgs";
    };
  };

  outputs = { self, nixpkgs, rust-overlay, ... }@inputs:
    let
      toolchain-channel = "stable";

      inherit (nixpkgs) lib;
      systems = [ "x86_64-linux" "aarch64-linux" ];
      eachSystem = f: lib.genAttrs systems f;
      pkgsFor = eachSystem
        (system:
          let
            rustPkgs = import nixpkgs {
              inherit system;
              overlays = [
                rust-overlay.overlays.default
              ];
            };
            inherit (rustPkgs) rust-bin;
          in
          import nixpkgs {
            inherit system;
            overlays = [
              (final: prev:
                {
                  rust-bin = rust-bin.${toolchain-channel};
                  rustPlatform =
                    let
                      toolchain = final.rust-bin.latest.minimal;
                    in
                    prev.makeRustPlatform {
                      cargo = toolchain;
                      rustc = toolchain;
                    };
                })
              self.overlays.default
            ];
          });
    in
    {
      overlays = import ./nix/overlays.nix { inherit self lib inputs; };

      packages = eachSystem (system:
        let
          pkgs = pkgsFor.${system};
        in
        {
          default = self.packages.${system}.sonorus;
          inherit (pkgs) sonorus sonorus-debug;
        });

      devShells = eachSystem (system:
        let
          pkgs = pkgsFor.${system};
        in
        {
          default = pkgs.callPackage ./nix/shell.nix { inherit self; };
        }
      );
    };
}
