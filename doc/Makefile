# Copyright (c) 2017, ETH Zurich
# All rights reserved.

# Redistribution and use in source and binary forms, with or without
# modification, are permitted provided that the following conditions are met:

# 1. Redistributions of source code must retain the above copyright notice, this
#    list of conditions and the following disclaimer.
# 2. Redistributions in binary form must reproduce the above copyright notice,
#    this list of conditions and the following disclaimer in the documentation
#    and/or other materials provided with the distribution.

# THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND
# ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
# WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
# DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT OWNER OR CONTRIBUTORS BE LIABLE FOR
# ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
# (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
# LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND
# ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
# (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
# SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.


ISABELLE=isabelle
RUN_ISABELLE=$(ISABELLE) build -N -j 4 
THEORIES_ROOT=../theories
BUILD_ROOT=../build
BUILD_PATH=$(BUILD_ROOT)/doc

DOCUMENTATION=machines.pdf model.pdf mipstlb.pdf

all: $(DOCUMENTATION)

machines.pdf : $(wildcard $(THEORIES_ROOT)/machines/*.thy) \
			   $(THEORIES_ROOT)/machines/root.tex
	$(RUN_ISABELLE) -D $(THEORIES_ROOT)/machines
	cp $(BUILD_PATH)/machines/document.pdf machines.pdf

model.pdf : $(wildcard $(THEORIES_ROOT)/model/*.thy) \
			$(THEORIES_ROOT)/model/root.tex
	$(RUN_ISABELLE) -D $(THEORIES_ROOT)/model
	cp $(BUILD_PATH)/model/document.pdf model.pdf

mipstlb.pdf : $(wildcard $(THEORIES_ROOT)/mipstlb/*.thy) \
			  $(THEORIES_ROOT)/mipstlb/root.tex
	$(RUN_ISABELLE) -D $(THEORIES_ROOT)/mipstlb 
	cp $(BUILD_PATH)/mipstlb/document.pdf mipstlb.pdf

clean: 
	rm -rf $(DOCUMENTATION)	
	rm -rf $(BUILD_ROOT)