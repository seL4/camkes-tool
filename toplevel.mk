#
# Copyright 2017, Data61
# Commonwealth Scientific and Industrial Research Organisation (CSIRO)
# ABN 41 687 119 230.
#
# This software may be distributed and modified according to the terms of
# the BSD 2-Clause license. Note that NO WARRANTY is provided.
# See "LICENSE_BSD2.txt" for details.
#
# @TAG(DATA61_BSD)
#

ifeq ($(wildcard tools/camkes),)
  $(error Directory 'tools/camkes' not present. Symlink this Makefile to the\
          top-level directory of the project and run `make` from there)
endif

ifeq (${PYTHONPATH},)
  export PYTHONPATH:=$(abspath tools/python-capdl)
else
  export PYTHONPATH:=${PYTHONPATH}:$(abspath tools/python-capdl)
endif
export PATH:=${PATH}:$(abspath tools/camkes)

lib-dirs:=libs

# Isabelle theory pre-processor.
export TPP:=$(abspath tools/camkes/tools/tpp)

# Build the loader image, rather than the default (app-images) because the
# loader image actually ends up containing the component images.
all: capdl-loader-experimental-image

-include Makefile.local

# Strip the quotes from the string CONFIG_CAMKES_IMPORT_PATH.
CAMKES_IMPORT_PATH=$(patsubst %",%,$(patsubst "%,%,${CONFIG_CAMKES_IMPORT_PATH}))
#")") Help syntax-highlighting editors.

export MAKEFLAGS += $(foreach p, ${CAMKES_IMPORT_PATH}, --include-dir=${p})

include tools/common/project.mk

capdl-loader-experimental: $(filter-out capdl-loader-experimental,$(apps)) ${STAGE_BASE}/parse-capDL/parse-capDL ${STAGE_BASE}/cpio-strip/cpio-strip
export CAPDL_SPEC:=$(foreach v,$(filter-out capdl-loader-experimental,${apps}),${BUILD_BASE}/${v}/${v}.cdl)

# The capdl translator is built in a custom environment to prevent compiler flags
# intended for the target affecting the compilation of haskell packages intended
# to run locally.
export PATH:=${PATH}:${STAGE_BASE}/parse-capDL
.PHONY: ${STAGE_BASE}/parse-capDL/parse-capDL
${STAGE_BASE}/parse-capDL/parse-capDL:
	@echo "[$(notdir $@)] building..."
	$(Q)env -i HOME=$(HOME) PATH=$(PATH) $(MAKE) --directory=tools/capDL sandbox
	$(Q)env -i HOME=$(HOME) PATH=$(PATH) $(MAKE) --directory=tools/capDL
	$(Q)env -i HOME=$(HOME) PATH=$(PATH) $(MAKE) --directory=tools/capDL install
	$(Q)mkdir -p "$(dir $@)"
	$(Q)cp -pR tools/capDL/$(notdir $@) $(dir $@)
	@echo "[$(notdir $@)] done."

export PATH:=${PATH}:${STAGE_BASE}/cpio-strip
${STAGE_BASE}/cpio-strip/cpio-strip:
	@echo "[$(notdir $@)] building..."
	$(Q)mkdir -p "$(dir $@)"
	$(Q)cp -p tools/common/cpio-strip.c $(dir $@)
	$(Q)cp -p tools/common/Makefile.cpio_strip $(dir $@)
	$(Q)Q=${Q} CC=gcc $(MAKE) --makefile=Makefile.cpio_strip --no-print-directory \
      --directory=$(dir $@) 2>&1 \
      | while read line; do echo " $$line"; done; \
      exit $${PIPESTATUS[0]}
	@echo "[$(notdir $@)] done."

# Fail a default `make` if the user has selected multiple apps.
ifeq (${MAKECMDGOALS},)
  ifeq ($(words $(filter-out capdl-loader-experimental,${apps})),0)
    $(error No CAmkES application selected)
  endif
  ifneq ($(words $(filter-out capdl-loader-experimental,${apps})),1)
    $(error Multiple CAmkES applications selected. Only a single application can be built at once)
  endif
endif

ifeq (${CONFIG_CAMKES_PRUNE_GENERATED},y)
${apps}: prune
endif
export PATH:=${STAGE_BASE}/pruner:${PATH}
PHONY += prune
prune: ${STAGE_BASE}/pruner/prune
CONFIG_CAMKES_LLVM_PATH:=$(CONFIG_CAMKES_LLVM_PATH:"%"=%)
ifeq (${CONFIG_CAMKES_LLVM_PATH},)
${STAGE_BASE}/pruner/prune: export CFLAGS=
else
  export PATH := ${CONFIG_CAMKES_LLVM_PATH}/bin:${PATH}
${STAGE_BASE}/pruner/prune: export CFLAGS=-I${CONFIG_CAMKES_LLVM_PATH}/include -L${CONFIG_CAMKES_LLVM_PATH}/lib
endif
${STAGE_BASE}/pruner/prune:
	@echo "[$(notdir $@)] building..."
	$(Q)mkdir -p "${STAGE_BASE}"
	$(Q)cp -pur tools/pruner $(dir $@)
	$(Q)CC="${HOSTCC}" $(MAKE) V=$V --no-print-directory --directory=$(dir $@) 2>&1 \
        | while read line; do echo " $$line"; done; \
        exit $${PIPESTATUS[0]}
	@echo "[$(notdir $@)] done."

# CapDL Isabelle representation. We falsely depend on the CapDL initialiser's
# image because the CapDL spec, that we *do* depend on, is not available as a
# target at the project level.
$(abspath ${BUILD_BASE})/$(filter-out capdl-loader-experimental,${apps})/thy/CapDLSpec.thy: capdl-loader-experimental-image ${STAGE_BASE}/parse-capDL/parse-capDL
	@echo "[GEN] $(notdir $@)"
	${Q}mkdir -p $(dir $@)
	${Q}${STAGE_BASE}/parse-capDL/parse-capDL --isabelle=$@ ${CAPDL_SPEC}
ifeq (${CONFIG_CAMKES_CAPDL_THY},y)
all: $(abspath ${BUILD_BASE})/$(filter-out capdl-loader-experimental,${apps})/thy/CapDLSpec.thy
endif

ifeq (${CONFIG_CAMKES_ACCELERATOR},y)
${apps}: ${STAGE_BASE}/accelerator/camkes-accelerator
export PATH:=${PATH}:${STAGE_BASE}/accelerator
ifeq (${V},1)
  CC_ACCELERATE_FLAGS += -D CMAKE_BUILD_TYPE=Debug
endif
ifeq (${V},2)
  CC_ACCELERATE_FLAGS += -D CMAKE_BUILD_TYPE=Debug
endif
ifeq (${V},3)
  CC_ACCELERATE_FLAGS += -D CMAKE_BUILD_TYPE=Debug
endif
ACCELERATE_EXTRA_DEPS := $(foreach f,$(shell ./tools/camkes/tools/accelerator/print-deps.py),$(wildcard ${f}))
${STAGE_BASE}/accelerator/camkes-accelerator: export CC=clang
${STAGE_BASE}/accelerator/camkes-accelerator: export CFLAGS=
${STAGE_BASE}/accelerator/camkes-accelerator: export LDFLAGS=
${STAGE_BASE}/accelerator/camkes-accelerator: \
  tools/camkes/tools/accelerator/accelerator.c \
  tools/camkes/tools/accelerator/CMakeLists.txt \
  tools/camkes/tools/accelerator/mkversion.py \
  ${ACCELERATE_EXTRA_DEPS}
	@echo "[$(notdir $@)] building..."
	${Q}mkdir -p $(dir $@)
	${Q}cd $(dir $@) && cmake -G Ninja ${CC_ACCELERATE_FLAGS} $(srctree)/tools/camkes/tools/accelerator
	${Q}cd $(dir $@) && ninja camkes-accelerator
endif

.PHONY: check-deps
check-deps:
	${Q}./tools/camkes/tools/check_deps.py
