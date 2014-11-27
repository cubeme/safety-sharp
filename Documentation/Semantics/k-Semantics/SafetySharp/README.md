# Examples

You can find examples in [\Examples\ModelFile](https://github.com/isse-augsburg/safety-sharp/tree/master/Examples/ModelFile).

You can create a symbolic link for more convenience when trying out one of the semantics: 

* ```ln -s Examples ../../../../../Examples/ModelFile``` (Linux) 
* ```mklink /d Examples ..\..\..\..\..\Examples\ModelFile``` (Windows)



# About the two different 

Here we suggest two possible ways to describe the semantics of safety sharp in the notation of the k Framework: The *pure* way and the *derived* way. The pure way sticks close to the written semantics of the semantics document. The derived way is easier to implement in a model checker and it is easier to reproduce what happens in small example models.

## pure way

You can find the pure semantics in the "semantics-pure" folder. Whenever a call of a provided port is made or a behaviour is executed, a new execution context is created.
```
<execution multiplicity="*">
	<currentVarValues> Map </currentVarValues>
	<currentComponent> Path </currentComponent>
	...
</execution>
```

Note:
 * ```<currentVarValues>``` is only a flat map from ids to values (no path)

 Pros:
	* resembles the written semantics more closely
	* allows implementation of recursion

Cons:
	* overkill, makes semantics harder to read

Idea how to implement:
When one of the rules (call), (beh), is called, create a new execution environment with needed program in its k-Cell. When it recognizes, that the new environment has final results (k-Cell is empty), use these results in the origin environment and remove the new environment. This could also be done for the rules (seq) and (cmd), but this seems to be a huge overkill. These two rules do not need their own variable environment. k offers a built-in way for sequential execution ( the ~> operator)
		

		
## derived way

There are several ways to derive the pure semantics to get a semantics which handles things a bit differently (i.e. closer to what could be interpreted by a model checker) but achieves the same results in concrete models.

1. Change the way local variables work: Only one global map for variables. When a new variable-context for (call) or (beh) is needed, prefix the corresponding key of this variable in the map <currentVarValues> with the path of the component and the function-call hierarchy. Also introduce an element in <execution> for the function-call hierarchy. When a function is called, all its current values are flushed away in <currentVarValues>. Also need to adapt the rule (assign_v) and the rule (getting the value of a variable in an expression) )
```
<execution>
	<currentVarValues> Map </currentVarValues>
	<currentComponent> Path </currentComponent>
	<currentCallStack> List </currentCallStack>
	...
</execution>
```

Note:
	* Only one execution context
	* ```<currentVarValues>``` contains the full call hierarchie ( (path of component). providedport1 . providedport2.variable)

Pros:
	* allows implementation of recursion
	* semantics easier to read
	* easier to implement here in k
	* transformation of the model checker also needs to do something similar, because variables cannot be introduced there arbitrarily

	  
2. Change the way local variables work: But in contrast to way 2 do not keep track of the function-call hierarchy. This leads to way less variables in the <currentVarValues>-map, but it also disallows recursion.
```
	<execution>
		<currentVarValues> Map </currentVarValues>
		<currentComponent> Path </currentComponent>
		<currentCall> Id </currentCall>
		...
	</execution>
```

Note:
	* ```<currentVarValues>``` contains the full component hierarchy and one port ( (path of component). providedport1.variable)

Pros:
	* easy to implement and read
	* no "stack" required

Cons:
	- less powerful (no recursion; that means also no "hidden" recursion, where a provided port calls a required port, which links to the same required port )
	- further away from regular imperative programming languages
