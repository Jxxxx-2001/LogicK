#!/bin/sh
set -eu
cd -- "$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)"
while IFS= read -r file || [ -n "$file" ]; do
    file=$(printf '%s' "$file" | tr -d '\r')
    case "$file" in
        ''|'#'*) continue ;;
    esac
    printf 'Compiling %s\n' "$file"
    coqc -I . "$file"
done < _CoqProject
