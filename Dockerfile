FROM ubuntu:22.04 as lib-base
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

RUN rm -rf /var/lib/apt/lists/*
RUN pip install --no-cache-dir -i https://pypi.tuna.tsinghua.edu.cn/simple \
        lark==0.12.0 \
        tblib==3.0.0 \
        z3-solver==4.13.0.0 \ 
        cvc5==1.2.0  


# RUN git config --global  http.https://github.com.proxy http://localhost:8118 \
#     && git config --global https.https://github.com.proxy  http://localhost:8118

RUN git clone https://github.com/bitwuzla/bitwuzla.git && \
    cd bitwuzla && \
    pip install .

# Builder Image for Veri-qec

FROM lib-base as builder
RUN mkdir /Veri-qec/
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

