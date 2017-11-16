.include "../../share/mk/top.mk"

# running the json schema test suite requires the jq tool to extract the
# tests into a format we can use to run
JQ ?= jq 

## JSON_SUITES are tests from the JSON schema test suite

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


## CUSTOM_SUITES are tests from our customized test suite
## in tests/jvst/custom

CUSTOM_SUITES.dir = tests/jvst

CUSTOM_SUITES  =
CUSTOM_SUITES += custom/anyOf


# Where to place the output...
TEST_OUTDIR.tests/jvst = ${BUILD}/tests/jvst


.if defined(JVST)

EXTRACT_SUITE = ${.CURDIR}/tests/jvst/extract.sh
RUN_SUITE     = ${.CURDIR}/tests/jvst/runtests.sh
REPORT_SUITE  = ${.CURDIR}/tests/jvst/reporttests.sh

SUITES = ${.CURDIR}/share/git/json-schema-test-suite/tests/draft6

cleansuite:
	rm -f ${.CURDIR}/${TEST_OUTDIR.tests/jvst}/results

mkjsonsuite:: mkdir cleansuite

jsonsuite:: mkjsonsuite ${JVST}

TEST_RESULTS.tests/jvst = ${TEST_OUTDIR.tests/jvst}/results

.for _s in ${JSON_SUITES}

${TEST_OUTDIR.tests/jvst}/${_s:S/.json//}: ${SUITES}/${_s}
	(cd ${TEST_OUTDIR.tests/jvst} && \
	 ${EXTRACT_SUITE} ${SUITES}/${_s} ${_s:S/.json//})

mkjsonsuite:: ${TEST_OUTDIR.tests/jvst}/${_s:S/.json//}

jsonsuite.${_s:S/.json//}:: ${TEST_OUTDIR.tests/jvst}/${_s:S/.json//}
	(						\
	  cd ${TEST_OUTDIR.tests/jvst} ; 		\
	  JVST=${.CURDIR}/${JVST} 			\
	  OUTFILE=${.CURDIR}/${TEST_RESULTS.tests/jvst}	\
	    ${RUN_SUITE} ${.ALLSRC:T}/* ; 		\
	)

jsonsuite:: jsonsuite.${_s:S/.json//}

.endfor

# default in case no custom suites are defined
customsuite:: mkdir cleansuite

.for _s in ${CUSTOM_SUITES}

customsuite.${_s}:: ${CUSTOM_SUITES.dir}/${_s}
	(						\
	  cd ${CUSTOM_SUITES.dir} ; 			\
	  JVST=${.CURDIR}/${JVST} 			\
	  OUTFILE=${.CURDIR}/${TEST_RESULTS.tests/jvst}	\
	    ${RUN_SUITE} ${_s}/*  			\
	)

customsuite:: customsuite.${_s}

.endfor

jsonsuite:: customsuite

jsonsuite:: 
	@echo Reporting results from ${TEST_RESULTS.tests/jvst}
	${REPORT_SUITE} ${TEST_RESULTS.tests/jvst}

.else  # !defined(JVST)

jsonsuite:
	echo "Cannot run json test suite without both jvst and jq"
	echo "JVST = ${JVST}"
	echo "JQ   = ${JQ}"

.endif # defined(JVST)
