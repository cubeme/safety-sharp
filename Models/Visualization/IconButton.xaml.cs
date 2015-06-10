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

namespace Visualization
{
	using System.Windows;
	using System.Windows.Media;

	public partial class IconButton
	{
		public static readonly DependencyProperty IconProperty = DependencyProperty.Register(
			"Icon", typeof(Visual), typeof(IconButton), new PropertyMetadata(default(Visual)));

		public static readonly RoutedEvent ClickedEvent = EventManager.RegisterRoutedEvent(
			"Clicked", RoutingStrategy.Bubble, typeof(RoutedEventHandler), typeof(IconButton));

		public IconButton()
		{
			InitializeComponent();
		}

		public Visual Icon
		{
			get { return (Visual)GetValue(IconProperty); }
			set { SetValue(IconProperty, value); }
		}

		public event RoutedEventHandler Clicked
		{
			add { AddHandler(ClickedEvent, value); }
			remove { RemoveHandler(ClickedEvent, value); }
		}

		private void OnClicked(object sender, RoutedEventArgs e)
		{
			RaiseEvent(new RoutedEventArgs(ClickedEvent));
		}
	}
}