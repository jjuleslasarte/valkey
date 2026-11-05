#!/usr/bin/env bash
# Runs Apalache 0.62.4 (needs Java 21; the host has 17) in a stock JRE container.
# Usage: tools/apalache.sh <apalache-mc args>   (run from the directory holding the .tla files)
T=$(cd "$(dirname "$0")" && pwd)
exec docker run --rm -u "$(id -u):$(id -g)" -v "$T/apalache-0.62.4:/opt/apalache:ro" \
  -v "$PWD:/work" -w /work -e JVM_ARGS="${JVM_ARGS:--Xmx16g}" \
  eclipse-temurin:21-jre /opt/apalache/bin/apalache-mc "$@"
