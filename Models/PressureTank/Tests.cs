﻿// The MIT License (MIT)
// 
// Copyright (c) 2014-2015, Institute for Software & Systems Engineering
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

namespace PressureTank
{
    using System;
    using System.Diagnostics;
    using NUnit.Framework;
    using SafetySharp.Analysis;

    [TestFixture]
    public class Tests
    {
        [SetUp]
        public void Initialize()
        {
            _model = new PressureTankModel();
        }

        private PressureTankModel _model;

        private static void Main()
        {
            var tests = new Tests();
            tests.Initialize();
            tests.FirstTest();
        }

        [Test]
        public void FirstTest()
        {
            var watch = new Stopwatch();
            watch.Start();
            var spin = new SpinModelChecker(_model);
            Console.WriteLine("Elapsed: {0}ms", watch.Elapsed.TotalMilliseconds);
        }
    }
}