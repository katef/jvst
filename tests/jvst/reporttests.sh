#! /bin/bash

declare -a failures
nsucc=0
nfail=0
ntot=0

in=$1

read nsucc0 nfail0 ntot0 < <(
awk -- 'BEGIN { ns = 0 ; nf = 0 ; nt = 0 }
  /^SUMMARY:/ { ns += $2 ; nf += $4 ; nt += $6 }
  END { print ns,nf,nt }' $in)

nsucc=$(( $nsucc + $nsucc0 ))
nfail=$(( $nfail + $nfail0 ))
ntot=$(( $ntot + $ntot0 ))

echo "TOTALS: ${nsucc} successes, ${nfail} failures, ${ntot} cases"
if [ ${nfail} -gt 0 ]; then
  echo "All failed tests:"
  (
  while read setname testname ; do
    printf "%-20.20s\t%s\n" "$setname" "$testname"
  done
  ) < <(grep -v '^SUMMARY\|^---\|^Failed tests:' $in)
fi

