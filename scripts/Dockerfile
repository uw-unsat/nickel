FROM ubuntu:18.04

RUN apt-get update && apt-get install -y g++ llvm clang python python-pip git

RUN pip2 install setproctitle pytest-xdist pytest-faulthandler

RUN git clone https://github.com/Z3Prover/z3.git z3

RUN cd z3 && git checkout z3-4.6.0 && python scripts/mk_make.py --prefix=/opt/z3 --pypkgdir=/opt/z3/lib/python-2.7/site-packages --python && cd build && make -j8 && make install

