#! /bin/sh

if [ -z "${JVST}" ]; then
  echo "JVST must be set"
  exit 1
fi

if [ -z "${OUTDIR}" ]; then
  echo "OUTDIR must be set"
  exit 1
fi

succ=0
skip=0
fail=0
ntest=0
ntotcase=0
while [ $# -gt 0 ]; do
  testdir=$1 ; shift
  schema=${testdir}/schema.json
  desc_file=${testdir}/description

  desc=`sed -e '1q' ${desc_file}`

  if [ ! -r $schema ]; then
    echo "cannot find schema in ${schema}"
    exit 1
  fi

  outcase=${OUTDIR}/${testdir}
  mkdir -p ${outcase}

  ncase=0
  succ_case=0
  fail_case=0
  skip_case=0

  printf " ---------[ %s: %s ]----------\n" "$testdir" "$desc"

  for testfile in ${testdir}/test_*.json ; do
    ncase=$(( $ncase + 1 ))
    ntotcase=$(( $ntotcase + 1 ))
    testbase=`basename ${testfile}`
    testbase=${testbase%.json}

    # XXX - direct this to ${BUILD} somehow...
    outfile=${OUTDIR}/${testdir}/${testbase}.out

    casenum=${testbase#test_}
    casenum=${casenum%_invalid}
    casenum=${casenum%_valid}

    casedesc=`awk -v CN=$casenum -- '$1 == CN { print }' < ${desc_file} | sed -e 's/^[0-9]\{1,\}[ 	]\{1,\}//'`

    ${JVST} -l jvst -c -r ${schema} ${testfile} > ${outfile} 2>&1
    valid=$?
    if [ $valid != 0 ]; then
      # standardize valid to be 0 (success) or 1 (failure)
      valid=1
    fi

    if [ "${testfile%_valid.json}_valid.json" = "${testfile}" ]; then
      expected=0
      expect_str="VALID"
    elif [ "${testfile%_invalid.json}_invalid.json" = "${testfile}" ]; then
      expected=1
      expect_str="INVALID"
    else
      # echo "unknown result for test ${testfile}"
      expected="skip"
      expect_str="<skip>"
    fi

    if [ $valid = 0 ]; then
      actual_str="VALID"
    else
      actual_str="INVALID"
    fi

    if [ $valid = $expected ]; then
      succ=$(( $succ + 1 ))
      succ_case=$(( $succ_case + 1 ))
      result="OK"
    elif [ "$expected" = "skip" ]; then
      skip=$(( $skip + 1 ))
      skip_case=$(( $skip_case + 1 ))
      result="SKIP"
    else
      fail=$(( $fail + 1 ))
      fail_case=$(( $fail_case + 1 ))
      result="FAILED"
    fi

    if [ "$COLORIZE" = "1" ]; then
      case $result in
        FAILED) clr="\\033[37;1;41m" ;;
        OK)     clr="\\033[32;1m" ;;
        SKIP)   clr="\\033[30;1;43m" ;;
        *)      clr="" ;;
      esac
      printf "\\033[37;1m%-18.18s\\033[0m\t%-40.40s\t${clr}[%s]\\033[0m\n" "$testbase" "$casedesc" "$result"
    else
      printf "%-18.18s\t%-40.40s\t[%s]\n" "$testbase" "$casedesc" "$result"
    fi

  done

  if [ ${succ_case} -lt ${ncase} ]; then
    echo "${testdir}: ${succ_case} successes, ${fail_case} failures, ${skip_case} skipped, ${ncase} cases"
  fi
done

nfail=$(( $ntotcase - $succ ))
echo "SUMMARY: ${succ} successes, ${nfail} failures, ${ntotcase} cases"
