# Makefile for extracting F* from SHA2 Rust implementation using hax
#
# Targets:
#   make extract - Extract F* code from Rust
#   make prove   - Verify the extracted F* code
#   make lax     - Lax check the extracted F* code
#   make clean   - Clean up generated files

# Directories
PROOF_DIR            := proofs/fstar
EXTRACTION_DIR       := $(PROOF_DIR)/extraction
CACHE_DIR            := .fstar-cache/checked
HINT_DIR             := .fstar-cache/hints

# F* configuration. Set HAX_LIB to point at a hax checkout (or rely on
# the dev shell exporting it).
HAX_LIB        ?= $(error HAX_LIB is not set — point it at a hax checkout, e.g. via the nix devShell)
FSTAR_BIN      ?= fstar.exe
FSTAR_FLAGS     = \
	--warn_error -321-331-241-274-239-271-242 \
	--silent \
	--cache_dir $(CACHE_DIR) \
	--hint_dir $(HINT_DIR) \
	--include $(EXTRACTION_DIR) \
	--include $(HAX_LIB)/proof-libs/fstar/core \
	--include $(HAX_LIB)/proof-libs/fstar/rust_primitives \
	--include $(HAX_LIB)/proofs/fstar/extraction

FSTAR := $(FSTAR_BIN) $(FSTAR_FLAGS)

CARGO_FEATURES := -C --no-default-features --features sha256 \;
RUSTFLAGS := --cfg sha2_backend=\"soft-compact\"

# Colors for output
BLUE   := \033[34m
BBLUE  := \033[1;34m
RESET  := \033[0m
RED    := \033[31m
GREEN  := \033[32m

.PHONY: all extract prove lax clean help vscode

# Default target
all: extract

help:
	@echo "SHA2 F* Extraction Makefile"
	@echo ""
	@echo "Available targets:"
	@printf "  $(BLUE)extract$(RESET)  - Extract F* code from Rust (SHA256 only, no dependencies)\n"
	@printf "  $(BLUE)prove$(RESET)    - Verify all extracted F* modules\n"
	@printf "  $(BLUE)lax$(RESET)      - Lax-check all extracted F* modules\n"
	@printf "  $(BLUE)clean$(RESET)    - Remove all generated files\n"
	@printf "  $(BLUE)help$(RESET)     - Show this help message\n"

# Extract F* code from Rust using hax
extract:
	@printf "$(BBLUE)[EXTRACT]$(RESET) Extracting F* from Rust code (soft backend)...\n"
	@mkdir -p $(EXTRACTION_DIR)
	@RUSTFLAGS="$(RUSTFLAGS)" cargo hax $(CARGO_FEATURES) into fstar
	@printf "$(GREEN)✓$(RESET) Extraction complete! Files are in $(EXTRACTION_DIR)\n"

# Verify the extracted F* code
prove:
	@printf "$(BBLUE)[VERIFY]$(RESET) Verifying extracted F* modules...\n"
	@mkdir -p $(CACHE_DIR) $(HINT_DIR)
	@if [ -z "$$(find $(EXTRACTION_DIR) -name '*.fst' -o -name '*.fsti')" ]; then \
		echo "$(RED)Error: No F* files found in $(EXTRACTION_DIR)$(RESET)"; \
		exit 1; \
	fi
	@for file in $(EXTRACTION_DIR)/*.fst $(EXTRACTION_DIR)/*.fsti; do \
		if [ -f "$$file" ]; then \
			printf "$(BLUE)[CHECK]$(RESET) $$(basename $$file)\n"; \
			$(FSTAR) $$file || exit 1; \
		fi; \
	done
	@printf "$(GREEN)✓$(RESET) All modules verified successfully!\n"

# Lax check the extracted F* code
lax:
	@printf "$(BBLUE)[LAX]$(RESET) Lax-checking extracted F* modules...\n"
	@mkdir -p $(CACHE_DIR) $(HINT_DIR)
	@if [ -z "$$(find $(EXTRACTION_DIR) -name '*.fst' -o -name '*.fsti')" ]; then \
		echo "$(RED)Error: No F* files found in $(EXTRACTION_DIR)$(RESET)"; \
		exit 1; \
	fi
	@for file in $(EXTRACTION_DIR)/*.fst $(EXTRACTION_DIR)/*.fsti; do \
		if [ -f "$$file" ]; then \
			printf "$(BLUE)[LAX]$(RESET) $$(basename $$file)\n"; \
			$(FSTAR) --lax $$file || exit 1; \
		fi; \
	done
	@printf "$(GREEN)✓$(RESET) Lax check complete!\n"

# Clean up generated files
clean:
	rm -f $(EXTRACTION_DIR)/*.fst $(EXTRACTION_DIR)/*.fsti

# Advanced: Generate VSCode configuration
vscode:
	@printf "$(BLUE)[VSCODE]$(RESET) Generating VSCode F* configuration...\n"
	@echo '{"fstar_exe": "$(FSTAR_BIN)", "include_dirs": ["$(EXTRACTION_DIR)"]}' | jq '.' > hax.fst.config.json
	@printf "$(GREEN)✓$(RESET) Generated hax.fst.config.json\n"
