#!/usr/bin/env bash
# Download the generated Lean proofs and unpack them under proofs/<q>/.
#
#   bash proofs/fetch.sh            # q9, q10, q11 and q12
#   bash proofs/fetch.sh q10        # one proof
#
# proofs/archives.tsv lists each archive's URL and SHA-256. An archive whose hash does not match
# is deleted and the script exits non-zero. ARCHIVE_DIR=<dir> takes the archives from a local
# directory instead of downloading them.
set -euo pipefail
cd "$(dirname "$0")"

want=("$@")
[ ${#want[@]} -gt 0 ] || want=(q9 q10 q11 q12)

sha256() { if command -v sha256sum >/dev/null; then sha256sum "$1"; else shasum -a 256 "$1"; fi | cut -d' ' -f1; }

mkdir -p archives
for q in "${want[@]}"; do
  line=$(awk -F'\t' -v q="$q" '$1 == q' archives.tsv)
  [ -n "$line" ] || { echo "no archive named $q in archives.tsv" >&2; exit 1; }
  file=$(cut -f2 <<<"$line"); url=$(cut -f3 <<<"$line"); hash=$(cut -f4 <<<"$line")
  dest="archives/$file"
  if [ -n "${ARCHIVE_DIR:-}" ]; then
    cp "$ARCHIVE_DIR/$file" "$dest"
  elif [ ! -f "$dest" ] || [ "$(sha256 "$dest")" != "$hash" ]; then
    case "$url" in *ZENODO_RECORD*) echo "archives.tsv has no download URL for $q yet" >&2; exit 1 ;; esac
    echo "downloading $file"
    curl -fL --retry 3 -o "$dest" "$url"
  fi
  got=$(sha256 "$dest")
  if [ "$got" != "$hash" ]; then
    echo "$file: sha256 $got, expected $hash; deleted" >&2
    rm -f "$dest"; exit 1
  fi
  rm -rf "$q"
  tar -xzf "$dest"
  echo "$q: $file verified, unpacked into proofs/$q"
done
