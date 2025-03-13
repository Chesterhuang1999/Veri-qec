FROM ubuntu:22.04 as lib-base
ENV DEBIAN_FRONTEND=noninteractive
RUN apt-get update && \
    apt-get -y --no-install-recommends install \
        cmake \
        make \
        clang \
        g++ \
        curl \
        default-jdk \
        python3 \
        build-essential \
        git \
        wget \
        autoconf \
        automake \
        libtool \
        libgmp-dev \
        zlib1g-dev \
        unzip \
        python3-setuptools \
        python-is-python3 \
        vim \
        python3-pip \
        sudo 

    
RUN rm -rf /var/lib/apt/lists/*
# RUN pip install tabulate
RUN pip install --no-cache-dir -r \
        lark=0.12.0 \
        z3-solver=4.13.0.0 \ 
        cvc5=1.2.0  

RUN git clone https://github.com/bitwuzla/bitwuzla.git && \
    cd bitwuzla && \
    pip install .

# Builder Image for Veri-qec

FROM lib-base as builder
RUN mkdir /Veri-qec/
RUN mkdir /Veri-qec/src
WORKDIR /Veri-qec
COPY ./src /Veri-qec/src
CMD ["/bin/bash"]
# CMD ["python", "execute_verify.py", "--cpucount 16", "--code surface", "--p1 7"]
# RUN pip install --no-cache-dir -r requirements.txt

# RUN git clone https://github.com/bitwuzla/bitwuzla.git
# WORKDIR /app/bitwuzla
# RUN pip install .
# WORKDIR /app 

