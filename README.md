# Hardware Models in Isabelle/HOL

This repository contains a formal model to represent the current hardware configuration (memory and interrupt subsystems) of a machine in Isabelle/HOL.

## Authors

See the AUTHORS file in the reposotiry.

## License

See the LICENSE file in the repository.


## Pre Requisites

Isabelle/HOL version 2016-1 
[[https://www.cl.cam.ac.uk/research/hvg/Isabelle/]]

Put the Isabelle binary into your search path such that it is found by Make

## Files
 * build: the build directory (created upon build)
 * doc: documentation directory (see Documentation)
 * theories: contains the Isabelle theories
    - machines: decoding nets for selected number of machines
    - mipstlb: the model for the MIPS TLB
    - model: the hardware model


## Documentation
The documentation can be built using `make documentation` or typing make in the
doc directory. This will produce a couple of PDF documents containing the
models and explanations.