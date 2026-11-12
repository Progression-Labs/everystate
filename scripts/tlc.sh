#!/bin/sh
# Run the reference Java TLC on a spec (oracle for differential testing).  usage: tlc.sh SPEC.tla CFG [extra flags]
spec="$1"; cfg="$2"; shift 2
dir=$(dirname "$spec"); meta=$(mktemp -d)
cd "$dir" && JAVA_TOOL_OPTIONS= java -XX:+UseParallelGC -DTLA-Library=/home/user/refs/tlapm/library:/home/user/refs/CommunityModules/modules -cp "${TLA2TOOLS:-/home/user/refs/tla2tools.jar}:${COMMUNITY_JAR:-}" tlc2.TLC -workers 1 -lncheck final -metadir "$meta" -config "$cfg" "$@" "$(basename "$spec")" 2>&1
rm -rf "$meta"
