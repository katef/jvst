#! /bin/sh

# uses jq to extract test cases from the json scheme test suite

if [ -z "${JQ+set}" ]; then
  JQ=`which jq`
fi

json=$1
if [ $# -ge 2 ]; then
  prefix=$2
else
  prefix=`basename ${json}`
  prefix=${prefix%.json}
fi

echo "JQ     ${JQ}"
echo "json   ${json}"
echo "prefix ${prefix}"

usage() {
  echo "$0 <dirname> <test.json>"
  exit 1
}

[ -z "$prefix" ] && usage
[ -z "${json}" ] && usage
[ -r "${json}" ] || usage

ntests=`${JQ} '.|length' ${json}`
echo "Found ${ntests} tests"

mkdir -p $prefix

i=0
while [ ${i} -lt ${ntests} ]; do
  mkdir -p $prefix/${i}
  fndesc=$prefix/${i}/description
  ${JQ} -r ".[${i}].description" ${json} > $fndesc
  ${JQ} -r ".[${i}].schema" ${json} > $prefix/${i}/schema.json
  ncases=`${JQ} ".[${i}].tests|length" ${json}`
  echo "test ${i} has ${ncases} cases"
  j=0
  while [ ${j} -lt ${ncases} ]; do
    desc=`${JQ} -r ".[${i}].tests[${j}].description" ${json}`
    valid=`${JQ} -r ".[${i}].tests[${j}].valid" ${json}`
    jstr=`printf '%03d' $j`
    if [ "${valid}" = "true" ]; then
      fn=${prefix}/${i}/test_${jstr}_valid.json
    else
      fn=${prefix}/${i}/test_${jstr}_invalid.json
    fi
    echo "${j}\t${desc}" >> $fndesc
    ${JQ} ".[${i}].tests[${j}].data" ${json} > ${fn}
    j=$(( $j + 1 ))
  done
  i=$(( $i + 1 ))
done

