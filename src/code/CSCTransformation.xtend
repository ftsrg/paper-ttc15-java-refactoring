package hu.bme.mit.ttc.refactoring.transformations

import TypeGraphBasic.TClass
import TypeGraphBasic.TMethodSignature
import TypeGraphBasic.TPackage
import TypeGraphBasic.TypeGraph
import TypeGraphBasic.TypeGraphBasicPackage
import com.google.common.collect.BiMap
import hu.bme.mit.ttc.refactoring.patterns.RefactoringQueries
import java.io.File
import java.util.ArrayList
import java.util.List
import java.util.Scanner
import java.util.Set
import org.apache.commons.lang3.StringUtils
import org.apache.log4j.Level
import org.eclipse.incquery.runtime.api.AdvancedIncQueryEngine
import org.eclipse.incquery.runtime.evm.api.RuleEngine
import org.eclipse.incquery.runtime.evm.specific.RuleEngines
import org.eclipse.incquery.runtime.evm.specific.event.IncQueryEventRealm
import org.eclipse.jdt.core.dom.ASTNode
import org.eclipse.jdt.core.dom.CompilationUnit
import org.eclipse.jdt.core.dom.MethodDeclaration
import org.eclipse.jdt.core.dom.Modifier.ModifierKeyword
import org.eclipse.jdt.core.dom.Name
import org.eclipse.jdt.core.dom.Type
import org.eclipse.jdt.core.dom.TypeDeclaration
import org.eclipse.viatra.emf.runtime.modelmanipulation.IModelManipulations
import org.eclipse.viatra.emf.runtime.modelmanipulation.SimpleModelManipulations
import org.eclipse.viatra.emf.runtime.rules.batch.BatchTransformationRuleFactory
import org.eclipse.viatra.emf.runtime.rules.batch.BatchTransformationStatements
import org.eclipse.viatra.emf.runtime.transformation.batch.BatchTransformation

class CSCTransformation {
	extension BatchTransformationRuleFactory factory = new BatchTransformationRuleFactory
	extension BatchTransformation transformation
	extension BatchTransformationStatements statements
	extension IModelManipulations manipulation

	extension TypeGraphBasicPackage tgPackage = TypeGraphBasicPackage::eINSTANCE
	extension RefactoringQueries queries = RefactoringQueries::instance
	
	val AdvancedIncQueryEngine engine
	val String concatSignature
	val String targetPackage
	val String targetName
	val BiMap<String, CompilationUnit> compilationUnits
	
	var CompilationUnit targetCU
	
	new(AdvancedIncQueryEngine engine, List<String> childClassSignatures, String targetPackage, String targetName, BiMap<String, CompilationUnit> compilationUnis) {
		this(RuleEngines.createIncQueryRuleEngine(engine), childClassSignatures, targetPackage, targetName, compilationUnis)
	}

	new(RuleEngine ruleEngine, List<String> childClassSignatures, String targetPackage, String targetName, BiMap<String, CompilationUnit> compilationUnits) {
		engine = (ruleEngine.eventRealm as IncQueryEventRealm).engine as AdvancedIncQueryEngine
		transformation = BatchTransformation.forEngine(engine)
		statements = new BatchTransformationStatements(transformation)
		manipulation = new SimpleModelManipulations(iqEngine)
		transformation.ruleEngine.logger.level = Level::OFF
		
		this.concatSignature = childClassSignatures.join("#")
		this.targetPackage = targetPackage
		this.targetName = targetName
		this.compilationUnits = compilationUnits
		
		compilationUnits.values.forEach[ try { it.recordModifications } catch (Exception e) {}]
	}
	
	val CSCRule = createRule.precondition(possibleCSC).action [
		val tClasses = engine.getMatcher(classesOfClassListTrace).getAllValuesOftClass(concatSignature)
		
		val List<TypeDeclaration> astChildClasses = findCompilationUnits(tClasses)
//		val methodDeclarations = findMethodDeclarations(astChildClasses, methodSignature)
		
		val firstChild = astChildClasses.get(0)
		
		if (targetCU == null) {
			targetCU = createTargetClass(firstChild, firstChild.superclassType)
		}
		
//		insertMethodDeclaration(methodDeclarations.get(0))
//		removeChildMethodDeclarations(methodDeclarations)
		setParentClass(astChildClasses)
		/// TODO should we add explicit dependency? (child classes import their new parent)
		
		serializeCUs
		
		
		// --------------- ▲ JDT transformation --------------- PG transformation ▼ ---------------
		
		val oldParentTClass = tClasses.get(0).parentClass
		if (oldParentTClass != null) {
			oldParentTClass.childClasses -= tClasses
		}
		
		val targetSignature = "L" + targetPackage.replace('.', '/') + "/" + targetName + ";";
		val typeGraph = engine.getMatcher(typeGraphs).oneArbitraryMatch.typeGraph
		
		val targetTClassMatch = engine.getMatcher(classWithName).getOneArbitraryMatch(null, targetSignature)
		var TClass targetTClass
		if (targetTClassMatch == null) {
			targetTClass = tgPackage.typeGraphBasicFactory.createTClass
			targetTClass.TName = targetSignature
			
			targetTClass.package = createPackagesFor(typeGraph, targetPackage)
			targetTClass.parentClass = oldParentTClass
		} else {
			targetTClass = targetTClassMatch.TClass
		}
		
		(tClasses.get(0).eContainer as TypeGraph).classes += targetTClass
		targetTClass.childClasses += tClasses
	].build
	
	protected def createPackagesFor(TypeGraph typeGraph, String pkg) {
		val String[] split = pkg.split("\\.");

		var previous = "";
		var TPackage previousTPackage
		for (var i = 0; i < split.length; i++) {
			var String current = previous
			if (i != 0)  {
				current += "."
			}
			current += split.get(i);

			var currentTPackageMatch = engine.getMatcher(packageWithName).getOneArbitraryMatch(null, current)
			if (currentTPackageMatch != null) {
				previousTPackage = currentTPackageMatch.TPackage
			} else {
				val TPackage currentTPackage = tgPackage.typeGraphBasicFactory.createTPackage
				currentTPackage.TName = current
				if (previousTPackage != null) {
					currentTPackage.parent = previousTPackage
				} else {
					typeGraph.packages += currentTPackage
				}
				
				previousTPackage = currentTPackage
			}
		}
		
		previousTPackage
	}
	
	protected def List<TypeDeclaration> findCompilationUnits(Set<TClass> childClasses) {
		val List<TypeDeclaration> astChildClasses = new ArrayList
		
		for (cu : compilationUnits.values) {
			for (child : childClasses) {
				if (cu.findDeclaringNode(child.TName) != null) {
					astChildClasses += cu.findDeclaringNode(child.TName) as TypeDeclaration
				}
			}
		}
		
		return astChildClasses
	}
	
	protected def List<MethodDeclaration> findMethodDeclarations(List<TypeDeclaration> astChildClasses, TMethodSignature tMethodSignature) {
		val List<MethodDeclaration> astMethodDeclarations = new ArrayList
		val methodSignatureTrace = engine.getMatcher(methodSignatureAndTrace).getAllValuesOftrace(tMethodSignature).get(0)
		
		for (childCU : astChildClasses) {
			val methodSignature = childCU.resolveBinding.key + methodSignatureTrace.signatureString;
			val types = (childCU.root as CompilationUnit).getStructuralProperty(CompilationUnit.TYPES_PROPERTY) as List<TypeDeclaration>
			for (type : types) {
				for (method : (type as TypeDeclaration).methods) {
//					println(method.resolveBinding.key)
//					println(methodSignature)
					if (method.resolveBinding.key.startsWith(methodSignature)) {
						astMethodDeclarations += method
//						println("MATCH")
					}
//					println
				}
			}
		}
		
		return astMethodDeclarations
	}
	
	protected def CompilationUnit createTargetClass(TypeDeclaration childClass, Type superClassType) {
//		val ast = AST.newAST(AST.JLS8)
		val ast = childClass.AST
		val compilationUnit = ast.newCompilationUnit
//		compilationUnit.recordModifications
		
		if (targetPackage != null) {
			val packageDeclaration = ast.newPackageDeclaration
			var Name packageName
			for (part : targetPackage.split("\\.")) {
				if (packageName == null) {
					packageName = ast.newSimpleName(part)
				} else {
					packageName = ast.newQualifiedName(packageName, ast.newSimpleName(part))
				}
			}
			packageDeclaration.name = packageName
			compilationUnit.package = packageDeclaration
		}
		
		compilationUnit.imports += ASTNode.copySubtrees(ast, (childClass.root as CompilationUnit).imports)
		
		val typeDeclaration = ast.newTypeDeclaration
		typeDeclaration.modifiers().add(ast.newModifier(ModifierKeyword.PUBLIC_KEYWORD))
		typeDeclaration.name = ast.newSimpleName(targetName)
		
		if (superClassType != null) {
			typeDeclaration.superclassType = ASTNode.copySubtree(ast, superClassType) as Type
		}
				
		compilationUnit.types += typeDeclaration
		
		compilationUnit
//		String targetSignature = "L" + target.getPackage().replace('.', '/') + "/" + target.getClass_name() + ";";
	}
	
	protected def insertMethodDeclaration(MethodDeclaration declaration) {
		val typeDeclaration = targetCU.types.get(0) as TypeDeclaration
		typeDeclaration.bodyDeclarations.add(ASTNode.copySubtree(targetCU.AST, declaration) as MethodDeclaration)
	}
	
	protected def setParentClass(List<TypeDeclaration> typeDeclarations) {
		val ast = targetCU.AST
		
		var Type fqn
		if (targetPackage != null) {
			for (part : targetPackage.split("\\.")) {
				if (fqn == null) {
					fqn = ast.newSimpleType(ast.newSimpleName(part))
				} else {
					fqn = ast.newQualifiedType(fqn, ast.newSimpleName(part))
				}
			}
			
			fqn = ast.newQualifiedType(fqn, ast.newSimpleName(targetName))
		} else {
			fqn = ast.newSimpleType(ast.newSimpleName(targetName))
		}
		
//		println(fqn)
		for (declaration : typeDeclarations) {
			declaration.superclassType = ASTNode.copySubtree(declaration.AST, fqn) as Type
		}
	}
	
	protected def removeChildMethodDeclarations(List<MethodDeclaration> methodDeclarations) {
		for (declaration : methodDeclarations) {
			declaration.delete
		}
	}
	
	def serializeCUs() {
		val targetDir = StringUtils.substringBefore(
								compilationUnits.keySet.get(0),
								"/src/"
							) + "/src/" + targetPackage.replace('.', '/')
		val targetPath = targetDir + "/" + targetName + ".java"
		
		val targetFile = new File(targetPath)
		targetFile.parentFile.mkdirs
		
		compilationUnits.put(targetPath, targetCU)
	}
	
	protected def readFileToString(String path) {
		new Scanner(new File(path)).useDelimiter("\\A").next
	}
	
	
	def fire() {
		fireAllCurrent(
			CSCRule,
			"concatSignature" -> concatSignature
			)
	}
	
	def canExecuteCSC() {
		val targetSignature = "L" + targetPackage.replace('.', '/') + "/" +  targetName + ";"
		val targetTClass = engine.getMatcher(classWithName).getOneArbitraryMatch(null, targetSignature)
		
		if (targetTClass != null) {
			return false
		}
		
		// TODO get the method signature by string, then get one arbitrary match with it bound
		engine.getMatcher(possibleCSC).countMatches > 0
	}
	
}