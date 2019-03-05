/**
 * @name cve-2018-11776 final
 * @description Final query for detecting CVE-2018-11776 in Struts.
 * @kind path-problem
 * @id cve_2018_11776_final
 */


import java
import lib.struts.DataFlow
import lib.struts.OGNL
import lib.struts.Sanitizers
import DataFlow::PathGraph

from MappingCfg cfg, DataFlow::PathNode source, DataFlow::PathNode sink
where cfg.hasFlowPath(source, sink)
select source, source, sink, "This user input flows to an $@.", sink, "OGNL sink"