package hu.bme.mit.ttc.refactoring.transformations

import TypeGraphBasic.TClass
import TypeGraphTrace.Trace
import TypeGraphTrace.TypeGraphTracePackage
import hu.bme.mit.ttc.refactoring.patterns.TraceQueries
import java.util.ArrayList
import java.util.List
import org.apache.log4j.Level
import org.eclipse.emf.ecore.resource.Resource
import org.eclipse.incquery.runtime.api.AdvancedIncQueryEngine
import org.eclipse.incquery.runtime.evm.api.RuleEngine
import org.eclipse.incquery.runtime.evm.specific.RuleEngines
import org.eclipse.incquery.runtime.evm.specific.event.IncQueryEventRealm
import org.eclipse.viatra.emf.runtime.modelmanipulation.IModelManipulations
import org.eclipse.viatra.emf.runtime.modelmanipulation.SimpleModelManipulations
import org.eclipse.viatra.emf.runtime.rules.batch.BatchTransformationRuleFactory
import org.eclipse.viatra.emf.runtime.rules.batch.BatchTransformationStatements
import org.eclipse.viatra.emf.runtime.transformation.batch.BatchTransformation

class TraceTransformation {

	extension BatchTransformationRuleFactory factory = new BatchTransformationRuleFactory
	extension BatchTransformation transformation
	extension BatchTransformationStatements statements
	extension IModelManipulations manipulation

//	extension TypeGraphBasicPackage tgbPackage = TypeGraphBasicPackage::eINSTANCE
	extension TypeGraphTracePackage tgtPackage = TypeGraphTracePackage::eINSTANCE
	extension TraceQueries queries = TraceQueries::instance
	val AdvancedIncQueryEngine engine
	Resource resource
	val Trace trace

	new(AdvancedIncQueryEngine engine, Resource resource) {
		this(RuleEngines.createIncQueryRuleEngine(engine), resource)
	}

	new(RuleEngine ruleEngine, Resource resource) {
		engine = (ruleEngine.eventRealm as IncQueryEventRealm).engine as AdvancedIncQueryEngine
		transformation = BatchTransformation.forEngine(engine)
		statements = new BatchTransformationStatements(transformation)
		manipulation = new SimpleModelManipulations(iqEngine)
		transformation.ruleEngine.logger.level = Level::OFF
		this.resource = resource
		this.trace = resource.contents.get(0) as Trace
	}

	val methodSignatureTraceRule = createRule.precondition(methodSignature).action [
		val methodSignatureTrace = typeGraphTraceFactory.createMethodSignatureTrace
		trace.methodSignatures += methodSignatureTrace

		val sb = new StringBuilder(".")
		sb.append(methodSignature.method.TName)
		sb.append("(")
		methodSignature.paramList.forEach[sb.append(it.TName)]
		sb.append(")")

		methodSignatureTrace.signatureString = sb.toString
		methodSignatureTrace.TMethodSignature = methodSignature
	].build
	
	
	def run() {		
		fireAllCurrent(methodSignatureTraceRule)
	}
	
	def addNewClassListTrace(List<String> classSignatures) {
		val List<TClass> tClasses = new ArrayList
		for (signature : classSignatures) {
			tClasses += engine.getMatcher(TClassName).getAllValuesOftClass(signature)
		}
		
		val classListTrace = typeGraphTraceFactory.createClassListTrace
		classListTrace.concatSignature = classSignatures.join("#")
		classListTrace.TClasses += tClasses
		
		trace.classLists += classListTrace
//		println(classListTrace.concatSignature)
//		println(classListTrace.TClasses)
//		println("classes: " + trace.programGraph.classes)
//		println("classList: " + trace.classLists)
//		println("trace: " + trace)
		return classListTrace
	}
}