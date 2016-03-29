#!/usr/bin/env bash

PORT="${1-8000}"
ROOT="static/"

echo "Serving $ROOT on :$PORT"
twistd --nodaemon web --path="$ROOT" --port="$PORT"
