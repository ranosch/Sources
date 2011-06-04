#!/bin/sh

exec ../Singular ext.sing 1> "EXT.`date`.log" 2>&1 &
