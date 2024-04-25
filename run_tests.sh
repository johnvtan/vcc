#!/bin/bash

make vcc

./testing/test_compiler ./compiler_driver.py "$@"
