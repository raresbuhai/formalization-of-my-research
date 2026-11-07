#!/usr/bin/env bash
# Download prebuilt Mathlib and complexitylib outputs, so that `lake build` doesn't compile them.
# CSLib has no published cache; the parts of it that are needed compile in a few minutes.
set -eu
cd "$(dirname "$0")/.."
lake exe cache get
url=https://storage.googleapis.com/complexitylib-lake-cache
LAKE_CACHE_ARTIFACT_ENDPOINT="$url/a0" LAKE_CACHE_REVISION_ENDPOINT="$url/r0" \
  lake cache get --repo=cslib-community/complexitylib --package=complexitylib
