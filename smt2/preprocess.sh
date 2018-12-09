#!/bin/sh
sed "$@" -e '1,/(set-info :status unsat)/d' -e '/(exit)/,/(exit)/d' -e 's/\?//g' -e 's/\./_dot_/g' -e 's/(\*/( */g' -e 's/|/_/g'
