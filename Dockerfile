FROM ubuntu:22.04 AS lib-base
ARG DEBIAN_FRONTEND=noninteractive
RUN sed -i 's|http://archive.ubuntu.com/ubuntu|http://mirrors.tuna.tsinghua.edu.cn/ubuntu|g' /etc/apt/sources.list && \
    sed -i 's|http://security.ubuntu.com/ubuntu|http://mirrors.tuna.tsinghua.edu.cn/ubuntu|g' /etc/apt/sources.list

RUN apt-get update && \
    apt-get -y --no-install-recommends install \
        cmake \
        make \
        clang \
        g++ \
        python3 \
        python3-dev \
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
        python3-pip 

RUN apt-get -y install ninja-build

RUN apt-get clean && \
    rm -rf /var/lib/apt/lists/*

RUN pip install -i https://pypi.tuna.tsinghua.edu.cn/simple \
        meson \ 
        cython \
        numpy \
        scipy \
        lark==1.1.9 \
        tblib==3.0.0 \
        timebudget==0.7.1 \
        galois==0.4.2 \
        z3-solver==4.13.0.0 \ 
        cvc5==1.2.0  

RUN meson --version

# RUN git config --global  http.proxy http://127.0.0.1:8118 \
#     && git config --global https.proxy  http://127.0.0.1:8118

# RUN git clone https://github.com/bitwuzla/bitwuzla.git && \
#     cd bitwuzla && \
#     pip install . && \
#     cd .. 

# Builder Image for Veri-qec

FROM lib-base AS builder
RUN mkdir /Veri-qec/
RUN mkdir /bitwuzla/
COPY ./bitwuzla/ /bitwuzla/
RUN cd bitwuzla && \
    pip install . --index-url https://pypi.tuna.tsinghua.edu.cn/simple && \
    cd ..

RUN mkdir /Veri-qec/src
RUN mkdir /Veri-qec/eval-Output
WORKDIR /Veri-qec
COPY ./src /Veri-qec/src
CMD ["/bin/bash"]
# CMD ["python", "execute_verify.py", "--cpucount 16", "--code surface", "--p1 7"]
# RUN pip install --no-cache-dir -r requirements.txt

# RUN git clone https://github.com/bitwuzla/bitwuzla.git
# WORKDIR /app/bitwuzla
# RUN pip install .
# WORKDIR /app 

