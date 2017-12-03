#!/bin/bash
#
# Usage: cat README.md | tools/most_freq_word.bash
#
# tr -c A-Za-z '\n' - replace all non words with \n

tr -cs A-Za-z '\n' | # all non-words to \n and then squeeze \n
tr A-Z a-z         | # all to lower-case
sort               |
uniq -c            |
sort -rn           |
sed ${1}q
