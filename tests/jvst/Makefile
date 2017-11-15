.include "../../share/mk/top.mk"

# running the json schema test suite requires the jq tool to extract the
# tests into a format we can use to run
JQ ?= jq 

JSON_SUITES = 
JSON_SUITES += type.json
JSON_SUITES += boolean_schema.json

JSON_SUITES += allOf.json
JSON_SUITES += anyOf.json
JSON_SUITES += oneOf.json
# JSON_SUITES += not.json

JSON_SUITES += items.json
JSON_SUITES += additionalItems.json
JSON_SUITES += contains.json
# JSON_SUITES += uniqueItems.json

JSON_SUITES += minItems.json
JSON_SUITES += maxItems.json

JSON_SUITES += minLength.json
JSON_SUITES += maxLength.json

JSON_SUITES += minProperties.json
JSON_SUITES += maxProperties.json

JSON_SUITES += exclusiveMinimum.json
JSON_SUITES += exclusiveMaximum.json

JSON_SUITES += minimum.json
JSON_SUITES += maximum.json

JSON_SUITES += multipleOf.json

JSON_SUITES += pattern.json

JSON_SUITES += properties.json
JSON_SUITES += patternProperties.json
JSON_SUITES += additionalProperties.json
JSON_SUITES += propertyNames.json

JSON_SUITES += required.json
JSON_SUITES += dependencies.json

JSON_SUITES += const.json
JSON_SUITES += enum.json

# JSON_SUITES += ref.json
# JSON_SUITES += definitions.json
# JSON_SUITES += refRemote.json

# JSON_SUITES += default.json

# JSON_SUITES += optional/bignum.json
# JSON_SUITES += optional/ecmascript-regex.json
# JSON_SUITES += optional/format.json
# JSON_SUITES += optional/zeroTerminatedFloats.json

.if defined(JVST)

EXTRACT_SUITE = ${.CURDIR}/tests/jvst/extract.sh
RUN_SUITE     = ${.CURDIR}/tests/jvst/runtests.sh
REPORT_SUITE  = ${.CURDIR}/tests/jvst/reporttests.sh

SUITES = ${.CURDIR}/share/git/json-schema-test-suite/tests/draft6

TEST_OUTDIR.tests/jvst = ${BUILD}/tests/jvst

SUBTEST += empty

mkjsonsuite:: mkdir
	rm -f ${.CURDIR}/${TEST_OUTDIR.tests/jvst}/results

jsonsuite:: mkjsonsuite ${JVST}

.for _s in ${JSON_SUITES}

${TEST_OUTDIR.tests/jvst}/${_s:S/.json//}: ${SUITES}/${_s}
	(cd ${TEST_OUTDIR.tests/jvst} && \
	 ${EXTRACT_SUITE} ${SUITES}/${_s} ${_s:S/.json//})

mkjsonsuite:: ${TEST_OUTDIR.tests/jvst}/${_s:S/.json//}

jsonsuite:: ${TEST_OUTDIR.tests/jvst}/${_s:S/.json//}
	(							\
	  cd ${TEST_OUTDIR.tests/jvst} ; 			\
	  JVST=${.CURDIR}/${JVST} 				\
	  OUTFILE=${.CURDIR}/${TEST_OUTDIR.tests/jvst}/results	\
	    ${RUN_SUITE} ${.ALLSRC:T}/* ; 			\
	)

.endfor

jsonsuite:: 
	@echo Reporting results in ${TEST_OUTDIR.tests/jvst}/results
	${REPORT_SUITE} ${TEST_OUTDIR.tests/jvst}/results

.else  # !defined(JVST)

jsonsuite:
	echo "Cannot run json test suite without both jvst and jq"
	echo "JVST = ${JVST}"
	echo "JQ   = ${JQ}"

.endif # defined(JVST)
