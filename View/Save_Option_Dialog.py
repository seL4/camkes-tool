#!/usr/bin/env python
# -*- coding: utf-8 -*-

from PyQt5 import QtWidgets, QtGui, QtCore


class SaveOptionDialog(QtWidgets.QDialog):

    PNG= 0
    SVG = 1

    def __init__(self, parent, proportional_rect=None):
        super(SaveOptionDialog, self).__init__(parent)

        self.format_combobox = QtWidgets.QComboBox(self)
        self.format_combobox.setInsertPolicy(QtWidgets.QComboBox.InsertAtBottom)
        self.format_combobox.addItem("Portable Network Graphics (*.png)")
        self.format_combobox.addItem("Scalable Vector Graphics (*.svg)")

        self.format_combobox.currentIndexChanged.connect(self.combox_changed)

        main_layout = QtWidgets.QVBoxLayout(self)
        main_layout.addWidget(self.format_combobox)

        # --- PNG Options ---

        self.png_options_widget = QtWidgets.QWidget(self)
        png_option_layout = QtWidgets.QVBoxLayout()

        # --- Width ---

        width_label = QtWidgets.QLabel("Width: ")
        px_label = QtWidgets.QLabel("px")
        self.width_lineedit = self.new_lineedits("Width in pixels")
        self.width_lineedit.textEdited.connect(self.width_changed)
        width_label.setBuddy(self.width_lineedit)

        width_hlayout = QtWidgets.QHBoxLayout()
        width_hlayout.addWidget(width_label)
        width_hlayout.addWidget(self.width_lineedit)
        width_hlayout.addWidget(px_label)

        png_option_layout.addLayout(width_hlayout)

        # --- Height ---

        height_label = QtWidgets.QLabel("Height: ")
        px_label2 = QtWidgets.QLabel("px")
        self.height_lineedit = self.new_lineedits("Height in pixels")
        self.height_lineedit.textEdited.connect(self.height_changed)
        height_label.setBuddy(self.height_lineedit)

        height_hlayout = QtWidgets.QHBoxLayout()
        height_hlayout.addWidget(height_label)
        height_hlayout.addWidget(self.height_lineedit)
        height_hlayout.addWidget(px_label2)

        png_option_layout.addLayout(height_hlayout)

        self.proportional_checkbox = QtWidgets.QCheckBox()
        self.proportional_checkbox.setText("Scale proportionally")
        self.proportional_checkbox.stateChanged.connect(self.proportional_state_change)

        png_option_layout.addWidget(self.proportional_checkbox)

        self.png_options_widget.setLayout(png_option_layout)
        main_layout.addWidget(self.png_options_widget)

        # --- SVG Options ---

        self.svg_option_widget = QtWidgets.QWidget(self)

        svg_option_layout = QtWidgets.QVBoxLayout()

        title_label = QtWidgets.QLabel("Title")
        self.title_lineedit = QtWidgets.QLineEdit()
        self.title_lineedit.setPlaceholderText("Type your title here")
        title_label.setBuddy(self.title_lineedit)

        svg_option_layout.addWidget(title_label)
        svg_option_layout.addWidget(self.title_lineedit)
        svg_option_layout.addSpacing(10)

        description_label = QtWidgets.QLabel("Description")
        self.descrip_textedit = QtWidgets.QTextEdit()
        self.descrip_textedit.setPlaceholderText("Type your description here")
        description_label.setBuddy(self.descrip_textedit)

        svg_option_layout.addWidget(description_label)
        svg_option_layout.addWidget(self.descrip_textedit)

        self.svg_option_widget.setLayout(svg_option_layout)

        main_layout.addWidget(self.svg_option_widget)

        self.svg_option_widget.setVisible(False)

        # --- Ok and Cancel buttons ---

        button_box = QtWidgets.QDialogButtonBox(QtWidgets.QDialogButtonBox.Ok | QtWidgets.QDialogButtonBox.Cancel)
        button_box.accepted.connect(self.accept)
        button_box.rejected.connect(self.reject)

        main_layout.addWidget(button_box)

        self.setLayout(main_layout)

        if proportional_rect:
            self.proportional_rect = proportional_rect


    def new_lineedits(self, placeholder):
        line_edit = QtWidgets.QLineEdit()
        line_edit.setPlaceholderText(placeholder)
        line_edit.setValidator(QtGui.QIntValidator())

        return line_edit

    def combox_changed(self, new_index):
        if new_index == self.PNG:
            self.svg_option_widget.setVisible(False)
            self.png_options_widget.setVisible(True)
        elif new_index == self.SVG:
            self.svg_option_widget.setVisible(True)
            self.png_options_widget.setVisible(False)

    def width_changed(self, text):
        if len(text) <= 0:
            return

        if self.proportional_checkbox.isChecked():
            assert isinstance(self.proportional_rect, QtCore.QRectF)
            width = int(text)
            height = self.proportional_rect.height() * width / self.proportional_rect.width()

            self.height_lineedit.setText(str(int(height)))

    def height_changed(self, text):
        if len(text) <= 0:
            return

        if self.proportional_checkbox.isChecked():
            assert isinstance(self.proportional_rect, QtCore.QRectF)
            height = int(text)
            width = self.proportional_rect.width() * height / self.proportional_rect.height()

            self.width_lineedit.setText(str(int(width)))

    def proportional_state_change(self, state):
        if state == QtCore.Qt.Checked:
            width = self.user_width()
            height = self.proportional_rect.height() * width / self.proportional_rect.width()
            self.width_lineedit.setText(str(int(width)))
            self.height_lineedit.setText(str(int(height)))

    def accept(self):

        if (self.width_lineedit.text() != "" \
                and self.height_lineedit.text() != "" \
                and int(self.width_lineedit.text()) != 0 \
                and int(self.height_lineedit.text()) != 0)\
                or self.format_combobox.currentIndex() == self.SVG:
            super(SaveOptionDialog, self).accept()

    def picture_type(self):
        return self.format_combobox.currentIndex()

    def user_width(self):
        try:
            return int(self.width_lineedit.text())
        except:
            return 0

    def user_height(self):
        try:
            return int(self.height_lineedit.text())
        except:
            return 0

    def user_title(self):
        return self.title_lineedit.text()

    def user_description(self):
        return self.descrip_textedit.toPlainText()