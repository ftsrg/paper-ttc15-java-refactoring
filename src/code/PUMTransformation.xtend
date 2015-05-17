package hu.bme.mit.ttc.refactoring.transformations

import TypeGraphBasic.TClass
import TypeGraphBasic.TypeGraphBasicPackage
import TypeGraphTrace.MethodSignatureTrace
import com.google.common.collect.BiMap
import hu.bme.mit.ttc.refactoring.patterns.PUMQueries
import java.io.File
import java.util.ArrayList
import java.util.List
import java.util.Scanner
import java.util.Set
import org.apache.log4j.Level
import org.eclipse.emf.ecore.util.EcoreUtil
import org.eclipse.incquery.runtime.api.AdvancedIncQueryEngine
import org.eclipse.incquery.runtime.evm.api.RuleEngine
import org.eclipse.incquery.runtime.evm.specific.RuleEngines
import org.eclipse.incquery.runtime.evm.specific.event.IncQueryEventRealm
import org.eclipse.jdt.core.dom.ASTNode
import org.eclipse.jdt.core.dom.CompilationUnit
import org.eclipse.jdt.core.dom.MethodDeclaration
import org.eclipse.jdt.core.dom.TypeDeclaration
import org.eclipse.viatra.emf.runtime.modelmanipulation.IModelManipulations
import org.eclipse.viatra.emf.runtime.modelmanipulation.SimpleModelManipulations
import org.eclipse.viatra.emf.runtime.rules.batch.BatchTransformationRuleFactory
import org.eclipse.viatra.emf.runtime.rules.batch.BatchTransformationStatements
import org.eclipse.viatra.emf.runtime.transformation.batch.BatchTransformation

class PUMTransformation {
	extension BatchTransformationRuleFactory factory = new BatchTransformationRuleFactory
	extension BatchTransformation transformation
	extension BatchTransformationStatements statements
	extension IModelManipulations manipulation

	extension TypeGraphBasicPackage tgPackage = TypeGraphBasicPackage::eINSTANCE
	extension PUMQueries queries = PUMQueries::instance
	
	val AdvancedIncQueryEngine engine
	val String parentSignature
	val String methodSignature
	val BiMap<String, CompilationUnit> compilationUnits
	
	new(AdvancedIncQueryEngine engine, String parentSignature, String methodSignature, BiMap<String, CompilationUnit> compilationUnis) {
		this(RuleEngines.createIncQueryRuleEngine(engine), parentSignature, methodSignature, compilationUnis)
	}

	new(RuleEngine ruleEngine, String parentSignature, String methodSignature, BiMap<String, CompilationUnit> compilationUnits) {
		engine = (ruleEngine.eventRealm as IncQueryEventRealm).engine as AdvancedIncQueryEngine
		transformation = BatchTransformation.forEngine(engine)
		statements = new BatchTransformationStatements(transformation)
		manipulation = new SimpleModelManipulations(iqEngine)
		transformation.ruleEngine.logger.level = Level::OFF
		
		this.parentSignature = parentSignature
		this.methodSignature = methodSignature
		this.compilationUnits = compilationUnits
		
		compilationUnits.values.forEach[ try { it.recordModifications } catch (Exception e) {}]
	}
	
	val PUMRule = createRule.precondition(possiblePUM).action [
		val parentClassKey = parentClass.TName
		val childClasses = engine.getMatcher(childClasses).getAllValuesOfchildClass(parentClass)
		
		var TypeDeclaration astParentClass
		var List<TypeDeclaration> astChildClasses = new ArrayList
		var List<MethodDeclaration> astMethodDeclarations
		
		astParentClass = findCompilationUnits(parentClassKey, childClasses, astChildClasses)
		astMethodDeclarations = findMethodDeclarations(astChildClasses, methodSignatureTrace)
		
		updateASTAndSerialize(astParentClass, astChildClasses, astMethodDeclarations)
		
		
		// --------------- /\ JDT transformation ------------- PG transformation \/ ---------------
		
		
		val methodDefinitionsToDelete = engine.getMatcher(methodDefinitionInClassList).getAllMatches(
			parentClass, methodSignatureTrace.TMethodSignature, null, null
		)
		
		val firstMethodDefinition = methodDefinitionsToDelete.get(0)
		val savedSignature = firstMethodDefinition.methodSignature
		val savedReturnType = firstMethodDefinition.methodDefinition.returnType
		val savedAccess = firstMethodDefinition.methodDefinition.access
		
		methodDefinitionsToDelete.forEach[
			it.clazz.signature.remove(it.methodDefinition.signature); // remove signature from class
			EcoreUtil.delete(it.methodDefinition, true)  // remove the method definition
		]
		
		val tMethodDefinition = tgPackage.typeGraphBasicFactory.createTMethodDefinition
		tMethodDefinition.returnType = savedReturnType
		tMethodDefinition.signature = savedSignature
		tMethodDefinition.access += savedAccess
		
		parentClass.defines += tMethodDefinition
		
		println(tMethodDefinition)
	].build
	
	protected def readFileToString(String path) {
		new Scanner(new File(path)).useDelimiter("\\A").next
	}
	
	protected def TypeDeclaration findCompilationUnits(String parentClassKey, Set<TClass> childClasses, List<TypeDeclaration> astChildClasses) {
		var TypeDeclaration result
		for (cu : compilationUnits.values) {
			// the just created CU can not resolve
			val firstTypeKey = "L"
						+ cu.package.name.fullyQualifiedName.replace('.', '/')
						+ "/"
						+ ((cu.types.get(0) as TypeDeclaration).name.fullyQualifiedName)
						+ ";"
						
			if (parentClassKey.equals(firstTypeKey)) {
				result = cu.types.get(0) as TypeDeclaration
			}

			for (child : childClasses) {
				if (firstTypeKey.equals(child.TName)) {
					astChildClasses += cu.types.get(0) as TypeDeclaration
				}
			}
		}
		
		return result
	}

	protected def List<MethodDeclaration> findMethodDeclarations(List<TypeDeclaration> astChildClasses, MethodSignatureTrace methodSignatureTrace) {
		val List<MethodDeclaration> astMethodDeclarations = new ArrayList
		
		for (childCU : astChildClasses) {
			val methodSignature = childCU.resolveBinding.key + methodSignatureTrace.signatureString;
			val types = (childCU.root as CompilationUnit).getStructuralProperty(CompilationUnit.TYPES_PROPERTY) as List<TypeDeclaration>
			for (type : types) {
				for (method : (type as TypeDeclaration).methods) {
					if (method.resolveBinding.key.startsWith(methodSignature)) {
						astMethodDeclarations += method
					}
				}
			}
		}
		
		return astMethodDeclarations
	}
	
	protected def updateASTAndSerialize(TypeDeclaration astParentClass, List<TypeDeclaration> astChildClasses, List<MethodDeclaration> astMethodDeclarations) {
		if (astMethodDeclarations.size > 0) {
			astParentClass.bodyDeclarations.add(ASTNode.copySubtree(astParentClass.AST, astMethodDeclarations.get(0)) as MethodDeclaration)
			
			for (methodDeclaration : astMethodDeclarations) {
				methodDeclaration.delete
			}
		}
	}
	
		def fire() {
		fireAllCurrent(
			PUMRule,
			"parentClass.tName" -> parentSignature,
			"MethodSignatureTrace.signatureString" -> methodSignature
			)
	}
	
	def canExecutePUM() {
		// get the method signature by string, then get one arbitrary match with it bound
		val parentTClass = engine.getMatcher(classWithName).getOneArbitraryMatch(null, parentSignature)
		val trace = engine.getMatcher(methodWithSignature).getOneArbitraryMatch(null, methodSignature)
		
		return
		parentTClass != null &&
		trace != null &&
		engine.getMatcher(possiblePUM).getOneArbitraryMatch(parentTClass.TClass, trace.trace) != null
	}
}