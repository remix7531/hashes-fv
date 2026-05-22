# Makefile for verifying SHA-2 with Aeneas + Lean.
#
# Targets:
#   make extract - Run Charon (Rust → LLBC) and Aeneas (LLBC → Lean)
#   make prove   - Build the Lean proofs (lake build)
#   make clean   - Remove generated LLBC and Lean files
#
# The Rust source is left untouched: Aeneas reads it as-is.

LEAN_DIR        := proofs/lean
EXTRACT_SUBDIR  := Extraction
LEAN_PKG        := $(LEAN_DIR)/$(EXTRACT_SUBDIR)
LLBC            := $(LEAN_DIR)/sha2.llbc

CHARON_OPTIONS  := --preset=aeneas \
	--rustc-arg=--allow=unused
AENEAS_OPTIONS  := -backend lean -split-files -abort-on-error \
	-subdir $(EXTRACT_SUBDIR) -namespace $(EXTRACT_SUBDIR)

# Translate the full SHA-256 path: the public `sha256` and `sha224` entry
# points in lib.rs, plus everything they call.
START_FROM      := \
	--start-from sha2::sha256 \
	--start-from sha2::sha224

CARGO_FEATURES  := --no-default-features --features "sha256,sha256_224"

# Colors for output
BLUE   := \033[34m
BBLUE  := \033[1;34m
RESET  := \033[0m
GREEN  := \033[32m

.PHONY: all extract prove clean help

all: extract prove

help:
	@echo "SHA-2 Aeneas+Lean verification Makefile"
	@echo ""
	@echo "Available targets:"
	@printf "  $(BLUE)extract$(RESET)  - Run Charon then Aeneas to regenerate Lean files\n"
	@printf "  $(BLUE)prove$(RESET)    - lake build the Lean proofs\n"
	@printf "  $(BLUE)clean$(RESET)    - Remove generated files\n"
	@printf "  $(BLUE)help$(RESET)     - Show this help message\n"

# Step 1: Charon translates Rust → LLBC
# Step 2: Aeneas translates LLBC → Lean
extract:
	@printf "$(BBLUE)[CHARON]$(RESET) Translating Rust → LLBC...\n"
	@mkdir -p $(LEAN_DIR)
	charon cargo $(CHARON_OPTIONS) --dest-file $(abspath $(LLBC)) $(START_FROM) -- $(CARGO_FEATURES)
	@printf "$(BBLUE)[AENEAS]$(RESET) Translating LLBC → Lean...\n"
	@mkdir -p $(LEAN_PKG)
	aeneas $(LLBC) $(AENEAS_OPTIONS) -dest $(LEAN_DIR)
	@printf "$(GREEN)✓$(RESET) Extraction complete. Generated files in $(LEAN_PKG)\n"

prove:
	@printf "$(BBLUE)[LAKE]$(RESET) Building Lean proofs...\n"
	cd $(LEAN_DIR) && lake build
	@printf "$(GREEN)✓$(RESET) All proofs check.\n"

clean:
	rm -f $(LLBC)
	rm -rf $(LEAN_PKG)
	rm -rf $(LEAN_DIR)/.lake/build
