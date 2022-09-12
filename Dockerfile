FROM ubuntu:focal as build
RUN apt-get update

# Install dependencies.
RUN apt-get install -y z3
RUN apt-get install -y libz3-dev
RUN apt-get install -y curl
RUN curl -sSL https://get.haskellstack.org/ | sh
RUN apt-get install -y git

# Fetch and build ORHLE.
RUN git clone https://github.com/rcdickerson/orhle.git
WORKDIR orhle
RUN git checkout aplas2022
RUN stack install

# Install Coq.
RUN apt-get install -y opam
RUN opam init --disable-sandboxing -y
RUN eval $(opam env) && opam pin add coq 8.15.2 -y

# Cleanup.
RUN stack clean --full
RUN rm -rf .stack-work
RUN rm -rf ~/.stack
RUN eval $(opam env) && opam clean -acs --logs
RUN rm -rf ~/.opam/repo
RUN apt-get clean

# Flatten.
FROM scratch
COPY --from=build / /
WORKDIR orhle

# Set the entry point.
ENTRYPOINT ["/root/.local/bin/orhle-exe"]
