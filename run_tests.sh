#!/bin/bash

make vcc

./testing/test_compiler ./bin/vcc "$@"
