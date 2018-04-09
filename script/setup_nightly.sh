#!/bin/false
# script should be sourced

git remote add nightly "https://$GH_TOKEN@github.com/leanprover/lean-nightly.git"
git fetch --all --tags
git checkout 8f55ec4

export LEAN_VERSION_STRING="nightly-2018-04-06"

# do nothing if commit is already tagged
if git checkout $LEAN_VERSION_STRING || ! git name-rev --name-only --tags --no-undefined HEAD
then
    # write into file since we repeatedly open and close shells on AppVeyor
    cat <<EOF > ./nightly.sh
export LEAN_VERSION_STRING=$LEAN_VERSION_STRING
EOF
    . ./nightly.sh
    OPTIONS+=" -DLEAN_SPECIAL_VERSION_DESC=$LEAN_VERSION_STRING"
else
    unset LEAN_VERSION_STRING
fi
