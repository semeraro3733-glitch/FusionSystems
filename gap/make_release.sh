#!/bin/sh
# Build the release archive FusionSystems-<version>.tar.gz of the GAP package
# (run from the directory containing pkg/FusionSystems).
set -e
cd "$(dirname "$0")"
VERSION=$(sed -n 's/^Version := "\(.*\)",/\1/p' pkg/FusionSystems/PackageInfo.g)
NAME="FusionSystems-$VERSION"
rm -rf "/tmp/$NAME" "$NAME.tar.gz"
mkdir -p "/tmp/$NAME"
cp -r pkg/FusionSystems/PackageInfo.g pkg/FusionSystems/init.g pkg/FusionSystems/read.g \
      pkg/FusionSystems/README.md pkg/FusionSystems/makedoc.g pkg/FusionSystems/lib \
      pkg/FusionSystems/tst pkg/FusionSystems/examples "/tmp/$NAME/"
mkdir -p "/tmp/$NAME/doc"
cp pkg/FusionSystems/doc/manual.xml pkg/FusionSystems/doc/FusionSystems.bib "/tmp/$NAME/doc/"
for f in pkg/FusionSystems/doc/*.html pkg/FusionSystems/doc/*.css pkg/FusionSystems/doc/*.js \
         pkg/FusionSystems/doc/manual.pdf pkg/FusionSystems/doc/manual.six pkg/FusionSystems/doc/manual.lab \
         pkg/FusionSystems/doc/*.txt; do
  [ -f "$f" ] && cp "$f" "/tmp/$NAME/doc/"
done
( cd /tmp && tar czf "$OLDPWD/$NAME.tar.gz" "$NAME" )
rm -rf "/tmp/$NAME"
echo "wrote $NAME.tar.gz"
