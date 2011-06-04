#!/bin/sh

exec ./regress.cmd -g -s ../Singular Old/2.lst 1> "OLD.`date`.log" 2>&1 &
