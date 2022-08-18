FROM ubuntu:focal
RUN apt-get update

# Install dependencies.
RUN apt-get install -y z3
RUN apt-get install -y libz3-dev
RUN apt-get install -y haskell-platform
RUN curl -sSL https://get.haskellstack.org/ | sh
RUN apt-get install -y git

# Fetch and build ORHLE.
RUN git clone https://github.com/rcdickerson/orhle.git
WORKDIR orhle
RUN git checkout 85e26d6fd0c413e84d0f87d1d23ac5dfc37b17d8
RUN stack install

# Set the entry point.
ENTRYPOINT ["/root/.local/bin/orhle-exe"]
