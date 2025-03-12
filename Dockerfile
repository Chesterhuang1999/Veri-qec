FROM ubuntu:22.04 as lib-base
ARG DEBIAN_FRONTEND=noninteractive
RUN apt-get update && \
    apt-get -y --no-install-recommends install \
        cmake \
        make \
        clang \
        g++ \
        curl \
        default-jdk \
        python3 \
        python3-setuptools \
        python-is-python3 \
        vim \
        python3-pip \
        sudo
RUN pip install tabulate

FROM python:3.9.18
WORKDIR /app
COPY . /app

RUN pip install --no-cache-dir -r requirements.txt

RUN git clone https://github.com/bitwuzla/bitwuzla.git
WORKDIR /app/bitwuzla
RUN pip install .
WORKDIR /app 

