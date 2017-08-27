#! /bin/sh

# uses jq to extract test cases from the json scheme test suite

if [ -z "${JQ+set}" ]; then
  JQ=`which jq`
fi

prefix=$1
json=$2

echo "JQ    =${JQ}"
echo "prefix=${prefix}"
echo "json  =${json}"

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
    if [ "${valid}" = "true" ]; then
      fn=${prefix}/${i}/test_${j}_valid.json
    else
      fn=${prefix}/${i}/test_${j}_invalid.json
    fi
    echo -e "${j}\t${desc}" >> $fndesc
    ${JQ} -r ".[${i}].tests[${j}].data" ${json} > ${fn}
    j=$(( $j + 1 ))
  done
  i=$(( $i + 1 ))
done

