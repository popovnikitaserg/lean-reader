FROM debian:bookworm-slim

RUN apt-get update && apt-get install -y --no-install-recommends \
    ca-certificates curl git wget xz-utils && \
    rm -rf /var/lib/apt/lists/*

ENV ELAN_HOME=/opt/elan
ENV CARGO_HOME=/opt/elan
ENV PATH=/opt/elan/bin:${PATH}

RUN curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | \
    sh -s -- -y --no-modify-path

WORKDIR /workspace
CMD ["lean"]
