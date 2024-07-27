#!/bin/bash

# Grab the directory of this script.
DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null 2>&1 && pwd )"

echo "Building binary (default features)..."
cargo build --release --bin howitzer

# Check if `docker` is installed
if ! command -v docker &> /dev/null
then
    echo "Error: docker not found. Please install docker and try again."
    exit
fi

echo "Building image..."
docker build -f howitzer.dockerfile "$DIR/.." -t howitzer:latest
