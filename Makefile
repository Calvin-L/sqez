SHELL=bash
SRC:=$(shell find src -iname '*.py')
TEST_SRC:=$(shell find tests -iname '*.py')
MK_DIR=.mk
.SUFFIXES:

.PHONY: help
help:
	@echo '---- Shortcuts for big tasks ----'
	@echo '  * make dist      : build a distribution'
	@echo '  * make clean     : delete all generated files'
	@echo '  * make deploy    : deploy release to PyPI'
	@echo '---- Shortcuts for small tasks ----'
	@echo '  * make tla       : check TLA+ designs'
	@echo '  * make typecheck : run mypy to typecheck'
	@echo '  * make test      : run tests'
	@echo '  * make check     : alias for `tla` + `typecheck` + `test`'
	@echo '  * make help      : show this help'

.PHONY: clean
clean:
	$(RM) -r '__pycache__'
	$(RM) -r '.mypy_cache'
	$(RM) -r '.pytest_cache'
	$(RM) -r 'designs/states'
	$(RM) -r 'designs/.tlacache'
	$(RM) -r 'dist'
	$(RM) -r '$(MK_DIR)'

.PHONY: tla typecheck test check dist
tla: $(MK_DIR)/tla.ok
typecheck: $(MK_DIR)/typecheck.ok
test: $(MK_DIR)/test.ok
check: tla typecheck test
dist: $(MK_DIR)/dist.ok

.PHONY: deploy
deploy: $(MK_DIR)/dist.ok
	python3 -m twine upload dist/*

$(MK_DIR)/Phaser_mc.ok: Makefile designs/Phaser.tla
	@mkdir -p '$(MK_DIR)'
	cd 'designs' && tlc2 -workers auto -config 'Phaser.tla' 'Phaser.tla'
	@touch '$@'

$(MK_DIR)/FairRWLock_mc.ok: Makefile designs/Phaser.tla designs/FairRWLock.tla $(MK_DIR)/Phaser_mc.ok
	@mkdir -p '$(MK_DIR)'
	cd 'designs' && tlc2 -workers auto -config 'FairRWLock.tla' 'FairRWLock.tla'
	@touch '$@'

$(MK_DIR)/FairRWLock_proofs.ok: Makefile designs/Phaser.tla designs/FairRWLock.tla designs/FairRWLockProofs.tla
	@mkdir -p '$(MK_DIR)'
	cd 'designs' && tlapm 'FairRWLockProofs.tla'
	@touch '$@'

$(MK_DIR)/tla.ok: $(MK_DIR)/Phaser_mc.ok $(MK_DIR)/FairRWLock_mc.ok $(MK_DIR)/FairRWLock_proofs.ok
	@touch '$@'

$(MK_DIR)/typecheck.ok: Makefile pyproject.toml $(SRC) $(TEST_SRC)
	@mkdir -p '$(MK_DIR)'
	mypy $(SRC) $(TEST_SRC)
	@touch '$@'

$(MK_DIR)/test.ok: Makefile pyproject.toml $(SRC) $(TEST_SRC)
	@mkdir -p '$(MK_DIR)'
	pytest
	@touch '$@'

$(MK_DIR)/dist.ok: Makefile pyproject.toml $(MK_DIR)/tla.ok $(MK_DIR)/typecheck.ok $(MK_DIR)/test.ok
	$(RM) -r dist
	python3 -m build
	@touch '$@'
