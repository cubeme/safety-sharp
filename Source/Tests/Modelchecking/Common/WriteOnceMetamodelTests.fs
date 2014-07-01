// The MIT License (MIT)
// 
// Copyright (c) 2014, Institute for Software & Systems Engineering
// 
// Permission is hereby granted, free of charge, to any person obtaining a copy
// of this software and associated documentation files (the "Software"), to deal
// in the Software without restriction, including without limitation the rights
// to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
// copies of the Software, and to permit persons to whom the Software is
// furnished to do so, subject to the following conditions:
// 
// The above copyright notice and this permission notice shall be included in
// all copies or substantial portions of the Software.
// 
// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
// IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
// FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
// AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
// LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
// OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
// THE SOFTWARE.

namespace SafetySharp.Tests.Modelchecking.Common.WriteOnceMetamodelTests


open NUnit.Framework
open Swensen.Unquote
open SafetySharp.Tests.Modelchecking

open SafetySharp.Utilities
open SafetySharp.Modelchecking


[<TestFixture>]
module WriteOnceTypeFieldManagerTests =
        
    [<Test>]
    let ``fieldManager initializes without exception`` () =
        let fieldManager=WriteOnceTypeFieldManager.Initialize(TestCase1Simplified.fields)
        ()
        
    [<Test>]
    let ``current redirection works for initial value`` () =
        let fieldToCheck = TestCase1Simplified.field
        let fieldManager=WriteOnceTypeFieldManager.Initialize([fieldToCheck])
        // check if old Field is in the _current_ Redirection Map
        let (redirectedTime,redirectedField) = fieldManager.getCurrentRedirection(fieldToCheck.getSimpleGlobalFieldWithContext)
        redirectedTime =? WriteOnceTimeOfAccess.UseResultOfLastStep
        redirectedField =? fieldToCheck
        // check the _new_ Redirection Map is empty
        let newArtificialFields = fieldManager.getNewArtificialFieldMapping
        newArtificialFields.Count =? 0
        

    [<Test>]
    let ``artificial value is created as expected`` () =
        let fieldToCheck = TestCase1Simplified.field
        let fieldManager=WriteOnceTypeFieldManager.Initialize([fieldToCheck])
        let (newField,newFieldManager) = fieldManager.createNewArtificialFieldForField(fieldToCheck.getSimpleGlobalFieldWithContext)
        newField <>? fieldToCheck
        // check if new Field is in the _current_ Redirection Map
        let (redirectedTime,redirectedField) = newFieldManager.getCurrentRedirection(fieldToCheck.getSimpleGlobalFieldWithContext)
        redirectedTime =? WriteOnceTimeOfAccess.UseResultOfThisStep
        redirectedField =? newField
        // check if new Field is in the _new_ Redirection Map
        let newArtificialFields = newFieldManager.getNewArtificialFieldMapping
        newArtificialFields.Count =? 1
        let (redirectedTime,redirectedField) = newArtificialFields.Item fieldToCheck.getSimpleGlobalFieldWithContext
        redirectedTime =? WriteOnceTimeOfAccess.UseResultOfThisStep
        redirectedField =? newField
        ()


