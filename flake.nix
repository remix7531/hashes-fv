{
  description = "rustcrypto-fv - RustCrypto formally-verified";

  inputs = {
    # Pinned to the immutable `sha2-fv-pin` tag (commit 3212a5fe) so the
    # Aeneas/Charon binaries stay locked to the same revision as the
    # Aeneas Lean library in sha2/proofs/lean/lake-manifest.json. The
    # `develop` branch on remix7531/aeneas is force-pushed, so referencing
    # it here would let the build break whenever upstream rewrites history.
    aeneas.url = "github:remix7531/aeneas/sha2-fv-pin";
    # Follow Aeneas's pinned nixpkgs and flake-utils so the toolchain shares
    # one set of inputs. rust-overlay is fetched directly.
    nixpkgs.follows = "aeneas/nixpkgs";
    flake-utils.follows = "aeneas/flake-utils";
    # Separate unstable channel for packages newer than Aeneas's pin —
    # currently `lean-lsp-mcp` (and its `leanclient` dep), which landed in
    # nixos-unstable but not yet in Aeneas's pinned nixpkgs.
    nixpkgs-unstable.url = "github:NixOS/nixpkgs/nixos-unstable";
    rust-overlay = {
      url = "github:oxalica/rust-overlay";
      inputs.nixpkgs.follows = "nixpkgs";
    };
  };

  outputs = { self, nixpkgs, nixpkgs-unstable, flake-utils, rust-overlay, aeneas, ... } @ inputs:
    flake-utils.lib.eachDefaultSystem (system:
      let
        overlays = [ (import rust-overlay) ];
        pkgs = import nixpkgs {
          inherit system overlays;
        };
        pkgsUnstable = import nixpkgs-unstable { inherit system; };
        rustToolchain = pkgs.rust-bin.nightly.latest.default;

        # MCP server — from nixos-unstable.
        lean-lsp-mcp = pkgsUnstable.lean-lsp-mcp;

        # Packages from nixpkgs. Note: `cargo`, `clippy`, and `rustfmt` are
        # NOT listed here — they ship with `rustToolchain` (the rust-overlay
        # nightly) and shadowing them with the nixpkgs versions causes
        # `rustc`/`clippy-driver` version skew (E0514) on dev-deps like
        # `hex-literal` when running `cargo clippy --all-targets`.
        nixpkgsPackages = with pkgs; [
          cargo-expand
          cargo-flamegraph
          cargo-show-asm
          elan
          jq
          pkg-config
          rust-analyzer
          rustToolchain
        ];

        # Packages from the Aeneas flake (Rust -> LLBC -> Lean toolchain)
        flakePackages = [
          aeneas.packages.${system}.aeneas
          aeneas.packages.${system}.charon
        ];
      in
      {
        devShells.default = pkgs.mkShell {
          buildInputs = nixpkgsPackages ++ flakePackages ++ [ lean-lsp-mcp ];

          shellHook = ''
            export RUST_BACKTRACE=1
          '';
        };

        packages = {
          default = pkgs.rustPlatform.buildRustPackage {
            pname = "rustcrypto-fv";
            version = "0.1.0";
            src = ./.;
            cargoLock.lockFile = ./Cargo.lock;
          };
        };
      }
    );
}
