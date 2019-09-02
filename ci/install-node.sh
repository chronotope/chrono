#!/usr/bin/env sh

echo "installing node via nvm"

source "$HOME/.nvm/nvm.sh"
nvm install 10
nvm use 10
curl https://rustwasm.github.io/wasm-pack/installer/init.sh -sSf | sh
