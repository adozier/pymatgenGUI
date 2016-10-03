#!/usr/bin/env python
"""
A graphical user interface that supports the basic functions of pymatgen,
including..

References:

Shyue Ping Ong, William Davidson Richards, Anubhav Jain, Geoffroy Hautier,
Michael Kocher, Shreyas Cholia, Dan Gunter, Vincent Chevrier,
Kristin A. Persson,Gerbrand Ceder.
Python Materials Genomics (pymatgen) : A Robust,
Open-Source Python Library for Materials Analysis.
Computationa Materials Science, 2013, 68, P. 314-319

 Menubar:

    File:
        open
        save
        save as
    Edit:
        cut
        copy
        paste
    Material Genie:
        Analyze VASP output directory tree- Extract computed properties
         from a VASP run tree using vasprun.xml files
        Analyze VASP output directory tree for ion magnetization-
            Extract computed properties for ion magnetization from a
            VASP run tree using vasprun.xml files
        Find Space Group, from POSCAR, CSSR, cif, or vasprun.xml-
            Find space group symmetry

buttons:

    Plot:
        Plot XMU.dat- Plot feff cross section
        Plot LDOS from FEFF LDOS00.dat file:
            Site- Plot feff LDOS density of states by site
            Element- Plot feff LDOS density of states by element
            Orbital- Plot feff LDOS density of states by orbital
        Plot DOS from vasprun.xml file:
            Site- Plot feff DOS density of states by site
            Element- Plot feff DOS density of states by element
            Orbital- Plot feff DOS density of states by orbital
        Plot Charge integration-  Plot charge integration
    View structure- visualization of selected structure
    Clear graph- clear graph
    Exit- destroy GUI window

    Find Materials- List materials from MP database using formula or elements
    Get Structure- Gets material structure object using material ID from MP
    database
    Browse- From file dialog opens a filename
    Create a feff.inp file:
        message box: Enter symbol of absorbing atoms
            Radio button- XANES or EXAFS
            Submit- converts structure to feff.inp file
            Cancel- destroys message box
    Display Structure- Displays structure summary
    Clear text- Clear text
    Exit- destroy GUI window
"""
from __future__ import division
#     from pymatgen.io.feff.sets import *
#     from pymatgen.io.feff import sets2
from pymatgen.io.vasp import *
from pymatgen.io.feff import *
from pymatgen.io.feff.outputs import LDos
from pymatgen.io.feff.sets import MPXANESSet
from pymatgen.core.structure import *
from pymatgen.io.cif import CifParser, CifWriter
from pymatgen.core.structure import Structure, Site, PeriodicSite
from pymatgen.util.coord_utils import in_coord_list
from pymatgen.core.periodic_table import Specie
from pymatgen.core.structure import Structure
from pymatgen.electronic_structure.core import Spin, Orbital
from collections import OrderedDict
from pymatgen.io.feff.outputs import LDos
from pymatgen.electronic_structure.plotter import DosPlotter
from pymatgen.electronic_structure.core import Spin
from pymatgen.core.structure import IStructure
from pymatgen.electronic_structure import dos
from pymatgen.vis.structure_vtk import StructureVis
from pymatgen.io.vasp import Outcar, Vasprun, Chgcar
from numpy import arange, sin, pi, average
from matplotlib.backends.backend_tkagg import FigureCanvasTkAgg, NavigationToolbar2TkAgg
from matplotlib.figure import Figure
from matplotlib.font_manager import FontProperties
from Tkinter import *
from PIL import Image
from PIL import ImageTk

import matplotlib
import pymatgen.io.feff.sets
import pymatgen.matproj.rest as mp
from pymatgen.io.cif import CifFile
import abc
import tkMessageBox
import Tkinter as Tk
import sys
import os
import subprocess
import tkFileDialog
import ConfigParser
import itertools
import math
import numpy as np
# import vtk


__author__ = "Megan LaRue"
__credits__ = "Alan Dozier, Shyue Ping Ong, Anubhav Jain"
__copyright__ = "Copyright 2011, The Materials Project"
__version__ = "1.3"
__maintainer__ = "Alan Dozier"
__email__ = "meganlarue79@gmail.com, alan1955@cinci.rr.com"
__status__ = "Beta"
__date__ = "September 13, 2014"

matplotlib.use('TkAgg')

pmg_dir = '~/GIT/pymatgen/pymatgen/cli'
current_dir = subprocess.Popen('pwd', shell=True, stdout=subprocess.PIPE)\
      .communicate()[0]
#pmg_dir = current_dir.replace('\n', '') + '/cli/pmg'

root = Tk.Tk()  # set Tk to root window (tree hierarchy) p.312

#       all the packages imported to run software

###############################################################################


class Graph_Window(Tk.Frame):
    """
    Creates a graphical visualization of the basic functions of pymatgen
    """

    def __init__(self, master):  # initialize constructor method (automatically invoked)
        """
        Initialize constructor method will automatically invoked the GUI frames
        including buttons and graph canvas

        Args:
            master:
                In Tkinter, master is a toplevel window manager and contains a given widgets
        """

        Tk.Frame.__init__(self, master, bd=2)  # bd means borderwidth

        self.pack()  # pack geometry manager-automatically places widgets in frame (rows and columns)
        # create a button frame

        frame = Frame(root)  # row of buttons
        frame.pack(anchor=NW)  # row of buttons

        self.xmu_ent = Tk.Entry(frame)
        self.ylimits = None

        # create buttons
        mbutton = Menubutton(frame, text='Plot')
        picks = Menu(mbutton)
        submenu2 = Menu(mbutton)
        submenu = Menu(mbutton)
        submenu3 = Menu(mbutton)
        submenu4 = Menu(mbutton)
        submenu5 = Menu(mbutton)
        mbutton.config(menu=picks)
        picks.add_command(label='plot XMU.dat', command=self.plotXMU)

        picks.add_cascade(label='Plot LDOS from FEFF LDOS00.dat file', menu=submenu2)

        submenu2.add_command(label='DOS by site', command=self.test_feff_site)
        submenu2.add_command(label='DOS by element', command=self.test_feff_element)
        submenu2.add_command(label='DOS by orbital', command=self.test_feff_orbital)

        picks.add_cascade(label='Plot DOS from vasprun.xml file', menu=submenu)

        submenu.add_command(label='DOS by site', command=self.test_vasp_dos_site)
        submenu.add_command(label='DOS by element', command=self.test_vasp_dos_element)
        submenu.add_command(label='DOS by orbital', command=self.test_vasp_dos_orbital)

        picks.add_cascade(label='Plot DOS from loaded MP-ID number', menu=submenu3)

        submenu3.add_command(label='DOS by site', command=self.MP_test_dos_site)
        submenu3.add_command(label='DOS by element', command=self.MP_test_dos_element)
        submenu3.add_command(label='DOS by orbital', command=self.MP_test_dos_orbital)

        picks.add_cascade(label='Compare FEFF with MP Orbital DOS', menu=submenu4)

        submenu4.add_command(label='S DOS', command=self.C_test_S)
        submenu4.add_command(label='P DOS', command=self.C_test_P)
        submenu4.add_command(label='D DOS', command=self.C_test_D)
        submenu4.add_command(label='F DOS', command=self.C_test_F)

        picks.add_command(label='Plot Charge integration', command=self.plotchgint)
        picks.add_command(label='Compare Occupied DOS with MP database file', command=self.occ_dos_compare)

        mbutton.pack(side=LEFT, fill=BOTH, expand=1)
        mbutton.config(bd=2, relief=RAISED)

        mbutton2 = Menubutton(frame, text='View 3D structure')
        picks2 = Menu(mbutton2)
        mbutton2.config(menu=picks2)
        picks2.add_command(label='view structure from file', command=self.view_structure)
        picks2.add_command(label='view loaded structure', command=self.view_current_structure)

        mbutton2.pack(side=LEFT, fill=BOTH, expand=1)
        mbutton2.config(bd=2, relief=RAISED)

#       b6 = Button(frame, text='view structure', command = self.view_structure)
#       b6.pack(side = LEFT, fill = BOTH, expand = 1)

        b3 = Button(frame, text='Clear graph', command=self.clear_graph)
        b3.pack(side=LEFT, fill=BOTH, expand=1)

        b4 = Button(frame, text='Exit', command=self._quit)
        b4.pack(side=LEFT, fill=BOTH, expand=1)

#       create file import
        self.file_opt = option = {}
        option['defaultextension'] = '.dat'
        option['filetypes'] = [('all files', '.*'), ('feff XMU.dat files', '*.dat')]
        option['initialdir'] = '../test_files'
        option['initialfile'] = ''
        option['parent'] = root
        option['title'] = 'Select file'

#       create graph and tool bar
        f = Figure(figsize=(5, 4), dpi=100)
        self.plt = f.add_subplot(111)
        self.color_order = ['r', 'b', 'g', 'c', 'k', 'm', 'y']
        self.fontp = FontProperties()

#        self._doses = OrderedDict()
#        self.all_dos = OrderedDict()
        self.stack = False
        self.zero_at_efermi = True

        self.canvas = FigureCanvasTkAgg(f, master=root)
#       self.canvas.show()
        self.canvas.get_tk_widget().pack(side=Tk.LEFT, fill=Tk.BOTH, expand=1)

        self.toolbar = NavigationToolbar2TkAgg(self.canvas, root)
        self.toolbar.update()
        self.canvas._tkcanvas.pack(side=Tk.LEFT, fill=Tk.BOTH, expand=1, padx=5)

    def test_feff_site(self):
        """
        Calls graph.feff_ldos with site -s option to plot ldos by sites in structure
        """
        option = '-s'
        Graph_Window.feff_ldos(gra, option)

    def test_feff_element(self):
        """
        Calls graph.feff_ldos with site -e option to plot ldos by elements in structure
        """
        option = '-e'
        Graph_Window.feff_ldos(gra, option)

    def test_feff_orbital(self):
        """
        Calls graph.feff_ldos with site -o option to plot ldos by orbital in structure
        """
        option = '-o'
        Graph_Window.feff_ldos(gra, option)

    def test_vasp_dos_site(self):
        """
        Calls graph.dos_plot with site -s option to plot dos by sites in structure
        """
        option = '-s'
        Graph_Window.dos_vasp_plot(gra, option)

    def test_vasp_dos_element(self):
        """
        Calls graph.dos_plot with site -e option to plot dos by elements in structure
        """
        option = '-e'
        Graph_Window.dos_vasp_plot(gra, option)

    def test_vasp_dos_orbital(self):
        """
        Calls graph.dos_plot with site -o option to plot dos by orbital in structure
        """
        option = '-o'
        Graph_Window.dos_vasp_plot(gra, option)

    def MP_test_dos_site(self):
        """
        Calls graph.dos_plot with site -s option to plot dos by sites in structure
        """
        option = '-s'
        Graph_Window.MP_dos_plot(gra, option)

    def MP_test_dos_element(self):
        """
        Calls graph.dos_plot with site -e option to plot dos by elements in structure
        """
        option = '-e'
        Graph_Window.MP_dos_plot(gra, option)

    def MP_test_dos_orbital(self):
        """
        Calls graph.dos_plot with site -o option to plot dos by orbital in structure
        """
        option = '-o'
        Graph_Window.MP_dos_plot(gra, option)

    def C_test_S(self):
        """
        Calls graph.dos_plot with site -o option to plot dos by orbital in structure
        """
        option = '-o'
        orbit = 's'
        Graph_Window.compare_plot(gra, option, orbit)

    def C_test_P(self):
        """
        Calls graph.dos_plot with site -o option to plot dos by orbital in structure
        """
        option = '-o'
        orbit = 'p'
        Graph_Window.compare_plot(gra, option, orbit)

    def C_test_D(self):
        """
        Calls graph.dos_plot with site -o option to plot dos by orbital in structure
        """
        option = '-o'
        orbit = 'd'
        Graph_Window.compare_plot(gra, option, orbit)

    def C_test_F(self):
        """
        Calls graph.dos_plot with site -o option to plot dos by orbital in structure
        """
        option = '-o'
        orbit = 'f'
        Graph_Window.compare_plot(gra, option, orbit)

    def compare_plot(self, option, orbit):

        Graph_Window.feff_ldos(gra, option, orbit)
        if Text_Window.mpID(cif) == '':
            tkMessageBox.showerror(title="No MP DOS Loaded", message = "Must Load MP Sructure")
            return
        else:
            Graph_Window.MP_dos_plot(gra, option, orbit)

    def plotXMU(self):
        """
        Plot feff cross section from xmu.dat files
        """
        file_name = tkFileDialog.askopenfilename(**self.file_opt)
        if file_name == '' or file_name == ():
            return
        self.xmu_ent.delete(0, END)
        self.xmu_ent.insert(0, file_name)
        # plot
        file_type = file_name.split(".")[-1]
        if file_type == 'dat':

            xmufile = self.xmu_ent.get()
            directory = ''
            directory_list = xmufile.split('/')
            for dir1 in directory_list[:-1]:
                directory = directory + '/' + dir1
            directory = directory[1:]
            feffinpfile = directory + '/feff.inp'

            xmu = Xmu.from_file(xmufile, feffinpfile)

            data = xmu.as_dict()
            x = np.array(data['data'])[:, 0].tolist()
            y = np.array(data['data'])[:, 4].tolist()
            x.pop()
            y.pop()
            tle = 'Single ' + data['absorbing_atom'] + ' ' + data['parameters']['EDGE'] + ' edge'
            self.plt.plot(x, y, self.color_order[1 % 7], label=tle)

            y = np.array(data['data'])[:, 3].tolist()
            y.pop()
            tle = data['absorbing_atom'] + ' ' + data['parameters']['EDGE'] + ' edge in ' + data['header']['source']
            self.plt.plot(x, y, self.color_order[2 % 7], label=tle)
            self.plt.set_title('XANES Cross Section')
            self.plt.set_xlabel('Energies eV')
            self.plt.set_ylabel('Absorption Cross-section')

            # fontp=FontProperties()
            self.fontp.set_size('x-small')
            self.plt.legend(prop=self.fontp, loc=0)

            self.canvas.show() 

        else:
            tkMessageBox.showerror(title="plot XMU", message="Must select xmu.dat file")
            self.xmu_ent.delete(0, Tk.END)

    def view_structure(self):
        """
        A visualization of a selected structure
        """
        file_name = tkFileDialog.askopenfilename(**self.file_opt)
        if file_name == '' or file_name == ():
            return
        self.xmu_ent.delete(0, END)
        self.xmu_ent.insert(0, file_name)

        xmu = self.xmu_ent.get()
        exe = 'python ' + pmg_dir + '/pmg.py view '

        subprocess.Popen(exe + xmu, shell=True, stdout=subprocess.PIPE)

#####################################################################

    def view_current_structure(self):
        """
        visualization of current structure
        """

        if Text_Window.struc(cif) != '':
            vis = StructureVis()
            vis.set_structure(Text_Window.struc(cif))
            vis.show()
        else:
            return

    def dos_plot_option(self, option, structure, dos, xlimits, sigma, orbit):
        S = OrbitalType.s
        P = OrbitalType.p
        D = OrbitalType.d
        F = OrbitalType.f
        if option == '-s':
            dp = DosPlotter(self.plt, True, False, sigma)
            mpe = dos.energies
            s1 = {}
            for site in dos.structure:
                site_dos = dos.get_site_dos(site)
                s1[site] = site_dos.get_densities(None)
            td = []
            for i in range(len(mpe)):
                t = 0.
                for site in s1:
                    t = t+s1[site][i]
                td.append(t)
            td = {Spin.up: td}
            d = {"efermi": dos.efermi, "energies": mpe, "densities": td}
            dos_obj = Dos.from_dict(d)
#            mpt = dos_obj.get_densities(None)
            mpt = dos.get_densities(None)
            tdos = {Spin.up: mpt}
            dos2 = Dos(dos.efermi, mpe, tdos)
            MP_new = CompleteDos(dos.structure, dos2, dos.pdos)
            dp.add_dos("Total", MP_new)
            for i in xrange(len(structure)):
                site = structure[i]
                dp.add_dos("Site " + str(i) + " " + site.specie.symbol,\
                           dos.get_site_dos(site))
            self.ylimits = None
            dp.get_plot(xlimits)

        if option == '-e':
            dp = DosPlotter(self.plt, True, False, sigma)
            mpe = dos.energies
            site_dos = dos.get_element_dos()
            s1 = {}
            for site in site_dos:
                s1[site] = site_dos[site].get_densities(None)
            td = []
            for i in range(len(mpe)-1):
                t = 0.
                for site in s1:
                    t = t+s1[site][i]
                td.append(t)
            td = {Spin.up: td}
            d = {'efermi': dos.efermi, 'energies': mpe, 'densities': td}
            dos_obj = Dos.from_dict(d)
#            mpt = dos_obj.get_densities(None)
            mpt = dos.get_densities()
            nelec = 0.
            for i in range(len(mpe)):
                if mpe[i] <= dos.efermi:
                    nelec = nelec + mpt[i]*(mpe[i+1]-mpe[i])
            print "# Elec = " + str(nelec)
            tdos = {Spin.up: mpt}
            dos2 = Dos(dos.efermi, mpe, tdos)
            MP_new = CompleteDos(dos.structure, dos2, dos.pdos)
            dp.add_dos("Total", MP_new)

            dp.add_dos_dict(dos.get_element_dos())
            dos_plot = dp.get_plot(xlimits)
            print "efermi = " + str(dos.efermi)

        if option == '-o':
            dp = DosPlotter(self.plt, False, False, sigma)
            if orbit == None:
                mpe = dos.energies
                dos_dict = dos.get_spd_dos()
                print dos_dict.keys()
                print dos_dict
                s = dos_dict[S].get_densities(None)
                p = dos_dict[P].get_densities(None)
                d = dos_dict[D].get_densities(None)
                mpt = []
                if F in dos_dict:
                    f = dos_dict[F].get_densities(None)
                for i in range(len(s)):
                    if F in dos_dict:
                        mpt.append(s[i]+p[i]+d[i]+f[i])
                    else:
                        mpt.append(s[i]+p[i]+d[i])
#                tdos = {Spin.up:mpt}
                tdos = dos.get_densities()
#                dos2 = Dos(dos.efermi, mpe, tdos)
                dos2 = Dos(dos.efermi, mpe, {Spin.up: tdos})
                MP_new = CompleteDos(dos.structure, dos2, dos.pdos)
                dp.add_dos("Total", MP_new)
                dp.add_dos_dict(dos.get_spd_dos())
                dos_plot = dp.get_plot(xlimits)
            if orbit == 's':
                spd_Dos = dos.get_spd_dos()
                d = {}
                d[S] = spd_Dos[S]
                dp.add_dos_dict(d)
                scale = False
                ccolor = False
                if self.ylimits:
                    scale = True
                    ccolor = True
                dos_plot = dp.get_plot(xlimits, self.ylimits, scale, ccolor)
                scale = False
                self.ylimits = dp.ylim
            if orbit == 'p':
                spd_Dos = dos.get_spd_dos()
                d = {}
                d[P] = spd_Dos[P]
                dp.add_dos_dict(d)
                scale = False
                ccolor = False
                if self.ylimits:
                    scale = True
                    ccolor = True
                dos_plot = dp.get_plot(xlimits, self.ylimits, scale, ccolor)
                scale = False
                self.ylimits = dp.ylim
            if orbit == 'd':
                spd_Dos = dos.get_spd_dos()
                d = {}
                d[D] = spd_Dos[D]
                dp.add_dos_dict(d)
                scale = False
                ccolor = False
                if self.ylimits:
                    scale = True
                    ccolor = True
                dos_plot = dp.get_plot(xlimits, self.ylimits, scale, ccolor)
                scale = False
                self.ylimits = dp.ylim
            if orbit == 'f':
                spd_Dos = dos.get_spd_dos()
                d = {}
                d[F] = spd_Dos[F]
                dp.add_dos_dict(d)
                ccolor = False
                scale = False
                if self.ylimits:
                    scale = True
                    ccolor = True
                dos_plot = dp.get_plot(xlimits, self.ylimits, scale, ccolor)
                scale = False
                self.ylimits = dp.ylim

    def feff_ldos(self, option, orbit=None):
        """
        Plot feff LDOS density of states from ldos.dat files

        Args:
            option:
                specifies whether plot by -s(site), -e(element), -o(orbital)
        """
        file_name = tkFileDialog.askopenfilename(**self.file_opt)
        if file_name == '' or file_name == ():
            return
        self.xmu_ent.delete(0, END)
        self.xmu_ent.insert(0, file_name)
        file_type = file_name.split(".")[-1]
        if file_type == 'dat':
            directory = ''
            directory_list = file_name.split('/')
            for dir1 in directory_list[:-1]:
                directory = directory + '/' + dir1
            directory = directory[1:]
            file_name = file_name[:-6]

            feffinpfile = directory + '/feff.inp'
            p = LDos.from_file(feffinpfile, file_name)
            dos = p.complete_dos
            energies = dos.energies
            tdos = dos.get_densities(None)
            sigma = .3

# find index of fermi energy
#            ifn = 0
#            while energies[ifn] <= dos.efermi:
#                ifn = ifn + 1
#            ifn = ifn + 4
# work backwards until slopes up
#            while ((tdos[ifn-1]-tdos[ifn])/(energies[ifn-1]-energies[ifn])) > -2.:
#                ifn -= 1

#            efermi_new = energies[ifn-2]
#            efermi_new = dos.efermi

#            tdos = {Spin.up:tdos}
#            dos2 = Dos(efermi_new, energies, tdos)
#            dos_new = CompleteDos(dos.structure, dos2 , dos.pdos)
#            f_info = 'old efermi = ' +str(dos.efermi) + ' new efermi =' + str(efermi_new)
#            print f_info
            structure = dos.structure
            xlimits = [-40, 15]
            self.dos_plot_option(option, structure, dos, xlimits, sigma, orbit)
#            self.dos_plot_option(option, structure, dos, xlimits, None, orbit)

            self.canvas.show()

        else:
            tkMessageBox.showerror(title="feff_ldos by site", message="Must select Ldos.dat file")
            self.xmu_ent.delete(0, Tk.END)

    def dos_vasp_plot(self, option, orbit=None):
        """
        Plot feff DOS density of states from vasprun.xml files

        Args:
            option:
                specifies whether plot by -s(site), -e(element), -o(orbital)
        """
        file_name = tkFileDialog.askopenfilename(**self.file_opt)
        if file_name == '' or file_name == ():
            return
        self.xmu_ent.delete(0, END)
        self.xmu_ent.insert(0, file_name)
        file_type = file_name.split(".")[-1]
        if file_type == 'xml':

            v = Vasprun(file_name)
            dos = v.complete_dos
            structure = v.final_structure
            xlimits = [-30, 30]
            self.dos_plot_option(option, structure, dos, xlimits, .2, orbit)

            self.canvas.show()

        else:
            tkMessageBox.showerror(title="dos by site",
                                   message="Must select vasprun.xml file")
            self.xmu_ent.delete(0, Tk.END)

    def MP_dos_plot(self, option, orbit=None):
        """
        Plot DOS density of states from MP ID number files

        Args:
            option:
                specifies whether plot by -s(site), -e(element), -o(orbital)
        """
        ID = Text_Window.mpID(cif)
        if ID == '':

            print 'Load MP Structure'
            return

        if ID != '':

            mpr = mp.MPRester("DIiNE4zmm8ATO0so")
            dos = mpr.get_dos_by_material_id(ID)
            structure = dos.structure
            xlimits = [-30, 30]
            self.dos_plot_option(option, structure, dos, xlimits, .3, orbit)

            self.canvas.show()

        else:
            tkMessageBox.showerror(title="Load MP Structure", message="Load MP Structure")

    def plotchgint(self):
        """
        Plot charge integration from CHGCAR files
        """
        file_name = tkFileDialog.askopenfilename(**self.file_opt)
        if file_name == '' or file_name == ():
            return
        self.xmu_ent.delete(0, END)
        self.xmu_ent.insert(0, file_name)
        file_name2 = file_name.split("/")[-1]
        file_type = file_name2.split(".")[0]
        if file_type == 'CHGCAR':

            chgcar = Chgcar.from_file(file_name)
            s = chgcar.structure

            finder = SpacegroupAnalyzer(s, symprec=0.1)
            sites = [sites[0] for sites in
                     finder.get_symmetrized_structure().equivalent_sites]
            atom_ind = [s.sites.index(site) for site in sites]

            for i in atom_ind:
                d = chgcar.get_integrated_diff(i, 3, 30)  # radius default is 3
                self.plt.plot(d[:, 0], d[:, 1],
                              label="Atom {} - {}".format(i, s[i].species_string))
            # self.plt.legend(loc="upper left")
            self.plt.set_xlabel("Radius (A)")
            self.plt.set_ylabel("Integrated charge (e)")

            self.fontp.set_size('x-small')
            self.plt.legend(prop=self.fontp, loc=0)

            self.canvas.show()

        else:
            tkMessageBox.showerror(title="plot charge integration", message="Must select CHGCAR file")
            self.xmu_ent.delete(0, Tk.END)

    def occ_dos_compare(self):
        """
        Plot Total density of states from MP ID number files and Feff ldos files
        Then shift, scale, and compute R^2
        """
        S = OrbitalType.s
        P = OrbitalType.p
        D = OrbitalType.d
        F = OrbitalType.f

        file_name = tkFileDialog.askopenfilename(**self.file_opt)
        if file_name == '' or file_name == ():
            return
        self.xmu_ent.delete(0, END)
        self.xmu_ent.insert(0, file_name)
        file_type = file_name.split(".")[-1]
        if file_type == 'dat':
            directory = ''
            directory_list = file_name.split('/')
            for dir1 in directory_list[:-1]:
                directory = directory + '/' + dir1
            directory = directory[1:]
            file_name = file_name[:-6]

            feffinpfile = directory + '/feff.inp'
            p = LDos.from_file(feffinpfile, file_name)
            dos_fraw = p.complete_dos
#            dos_dict = dos_fraw.get_smeared_densities(.3)
            fe = dos_fraw.energies
#            d = {"efermi":dos_fraw.efermi, "energies":fe, "densities": dos_dict}
#            dos_obj = Dos.from_dict(d)
#            tdos = dos_obj.get_densities(None)
            dos_dict = dos_fraw.get_spd_dos()
            s = dos_dict[S].get_densities()
            p = dos_dict[P].get_densities()
            d = dos_dict[D].get_densities()
            f = dos_dict[F].get_densities()
            tdos = []
            for i in range(len(s)):
                tdos.append(s[i]+p[i]+d[i]+f[i])
#            structure = p.complete_dos.structure
            xlimits = [-40, 15]
            dp = DosPlotter(self.plt, False, False)
#            dp.add_dos("Total", dos)
#            dos_plot = dp.get_plot(xlimits)

        else:
            tkMessageBox.showerror(title="feff_ldos by site", message="Must select Ldos.dat file")
            self.xmu_ent.delete(0, Tk.END)

        ID = Text_Window.mpID(cif)
        if ID == None:
            print 'Load MP Structure'
            return

        mpr = mp.MPRester("DIiNE4zmm8ATO0so")
        dos_raw = mpr.get_dos_by_material_id(ID)
        mpe = dos_raw.energies
#        dos_dict = dos_raw.get_smeared_densities(.4)
#        d = {"efermi":dos_raw.efermi, "energies":mpe, "densities":dos_dict}
#        dos_obj = Dos.from_dict(d)
#        mpt = dos_obj.get_densities(None)
#        tdos = {Spin.up: mpt}
#        dos2 = Dos(dos_raw.efermi, mpe, tdos)
#        dos = CompleteDos(dos_raw.structure, dos2 , dos_dict)
        dos_dict = dos_raw.get_spd_dos()
        s = dos_dict[S].get_densities()
        p = dos_dict[P].get_densities()
        d = dos_dict[D].get_densities()

        mpt = []
        for i in range(len(s)):
            mpt.append(s[i]+p[i]+d[i])
        mpt = dos_raw.get_densities()
        nelec_mp = 0.
        for i in range(len(mpe)):
            if mpe[i] <= dos_raw.efermi:
                nelec_mp = nelec_mp + mpt[i]*(mpe[i+1]-mpe[i])
        print "# Elec in MP Raw Data = " + str(nelec_mp)
#        Extend MP energy scale to match feff ldos
        de = mpe[1]-mpe[0]
        smpe = []
        mpto = []
        xlen = np.shape(mpe)[0]
        if mpe[0] > fe[0]:
            for i in range(xlen):
                E = fe[0] + i * de
                if E < mpe[0]:
                    smpe.append(E)
                    mpto.append(0.)

            smpe = np.array(smpe)
            mpe = np.hstack([smpe, mpe])
            mpto = np.array(mpto)
            mpt = np.hstack([mpto, mpt])

# Set up feff dos object
        fto = tdos
        efermi_feff = dos_fraw.efermi
        tdos = {Spin.up: fto}
        dos2 = Dos(efermi_feff, fe, tdos)
        dos_dict_feff = dos2.get_smeared_densities(.3)
        fto = dos_dict_feff[Spin.up]
#        dos_feff = CompleteDos(dos_fraw.structure, dos2 ,dos_dict)
        f_info = 'FEFF efermi =' + str(efermi_feff)
        print f_info

#        Set up MP dos object
        dos3 = Dos(dos_raw.efermi, mpe, {Spin.up: mpt})
        dos_dict = dos3.get_smeared_densities(.5)
        mpt = dos_dict[Spin.up]
#        d = {"efermi":dos_raw.efermi, "energies":mpe, "densities":dos_dict}
#        dos_obj = Dos.from_dict(d)
#        mpt = dos_obj.get_densities(None)
#        tdos = {Spin.up: mpt}
#        dos2 = Dos(dos_raw.efermi, mpe, tdos)
#        dos = CompleteDos(dos_raw.structure, dos_obj , dos_dict)
        efermi_mpe = dos_raw.efermi
        f_info = 'MP efermi =' + str(efermi_mpe)
        print f_info
#            dp = DosPlotter(self.plt, True, False, .3)

        ifermi = 0
        iefermi_mpe_exact = 0
        iefermi_feff_exact = 0
        istart = 0
        iend = 0

        for E in mpe:

            if E <= fe[0]:
                istart = istart + 1
            if E <= (10. + efermi_mpe):
                iend = iend + 1
            if E <= efermi_mpe:
                iefermi_mpe_exact = iefermi_mpe_exact + 1
            if E <= efermi_feff:
                iefermi_feff_exact = iefermi_feff_exact + 1
            if E <= 4. + efermi_feff:
                ifermi = ifermi + 1

        ft = []
        for E in mpe:
            if (E < fe[0]) or (E > fe[-1]):
                ft.append(0)
            else:
                fy = np.interp(E, fe, fto)
                ft.append(fy)

        [Chi2minleft, Chi2minright, ishiftleft, ishiftright, mptnew] =\
            self.r2(ifermi, iefermi_mpe_exact, iefermi_feff_exact, istart, iend, mpt, mpe, ft)
        iefermi_mpe_exact_new = 0
        iendnew = -1
        if Chi2minleft <= Chi2minright:
            eshift = mpe[0]-mpe[ishiftleft]
        else:
            eshift = mpe[ishiftright]-mpe[0]

        for E in mpe:
            if E < (10. + efermi_mpe+eshift):
                iendnew = iendnew + 1
            if E <= efermi_mpe+eshift:
                iefermi_mpe_exact_new = iefermi_mpe_exact_new + 1

        [Chi2minleftnew, Chi2minrightnew, ishiftleftnew, ishiftrightnew, mptnew]=\
            self.r2(ifermi, iefermi_mpe_exact_new, iefermi_feff_exact, istart, iendnew, mptnew, mpe, ft)

        nfelec = 0.
        nelect_list = mpr.query(cif.source, ["input.parameters.NELECT"])
        nelect = nelect_list[0][u'input.parameters.NELECT']

        for i in range(iefermi_feff_exact-istart):
            nfelec = nfelec + ft[i+istart]*(mpe[i+istart+1]-mpe[i+istart])
        if Chi2minleft < Chi2minright:

            Text_Window.print_text(cif, 'Feff Directory - ' + directory +
                                   '\nCompound - ' + dos_fraw.structure.formula +
                                   '\nMP ID = ' + str(ID) +
                                   '\nShift left = ' + str(mpe[0]-mpe[ishiftleft]) + ' Volts' +
                                   '\nR2 = ' + str(1.-Chi2minleft) +
                                   '\nFeff efermi = ' + str(efermi_feff) +
                                   '\nMP efermi = ' + str(dos_raw.efermi) +
                                   '\nDiff = ' + str(efermi_feff-dos_raw.efermi) + 'Volts'  +
                                   '\n# FEFF electrons = ' + str(nfelec) +
                                   '\n# VASP electrons from input NELECT = ' + str(nelect) +
                                   '\n# VASP electrons from MP raw data = ' + str(nelec_mp))
        else:
            Text_Window.print_text(cif, 'Feff Directory - ' + directory +
                                   '\nCompound - ' + dos_fraw.structure.formula +
                                   '\nMP ID = ' + str(ID) +
                                   '\nShift right = ' + str(mpe[ishiftright]-mpe[0]) + ' Volts' +
                                   '\nR2 = ' + str(1-Chi2minright) +
                                   '\nFeff efermi = ' + str(efermi_feff) +
                                   '\nMP efermi = ' + str(dos_raw.efermi) +
                                   '\nDiff = ' + str(efermi_feff-dos_raw.efermi) + 'Volts' +
                                   '\n# FEFF electrons = ' + str(nfelec) +
                                   '\n# VASP electrons from input NELECT = ' + str(nelect) +
                                   '\n# VASP electrons from MP raw data = ' + str(nelec_mp))

        tdos = {Spin.up: ft}
        dos2 = Dos(efermi_feff, mpe, tdos)
#        feff_new = CompleteDos(dos_fraw.structure, dos2, dos_feff.pdos)
        dp.add_dos("FEFF", dos2)

        tdos = {Spin.up: mptnew}
        dos2 = Dos(dos_raw.efermi, mpe, tdos)
#            = CompleteDos(dos_raw.structure, dos2 , dos.pdos)
        dp.add_dos("MP", dos2)

        dos_plot = dp.get_plot(xlimits)

        self.canvas.show()

    def r2(self, ifermi, iefermi_mpe_exact, iefermi_feff_exact, istart, iend, mpt, mpe, ft):
        nelec = 0.
        nfelec = 0.

        for i in range(iefermi_mpe_exact-istart):
            nelec = nelec + mpt[i+istart]*(mpe[i+istart+1]-mpe[i+istart])
        print "MP # Elec = " + str(nelec)

        mpr = mp.MPRester("DIiNE4zmm8ATO0so")
        nelect_list = mpr.query(cif.source, ["input.parameters.NELECT"])
        nelect = nelect_list[0][u'input.parameters.NELECT']
        print "VASP #electrons from input = " + str(nelect)

        for i in range(iefermi_feff_exact-istart):
            nfelec = nfelec + ft[i+istart]*(mpe[i+istart+1]-mpe[i+istart])
        print "FEFF # Elec = " + str(nfelec)

        ishiftmax = iend - istart
        Chi2minleft = 0.
        Chi2minright = 0.
        xlen = np.shape(mpe)[0]
        ave = 0.
#        ave_mpt = 0.
        ishiftleft = 0
        ishiftright = 0

        for ie in range(len(mpe)):
            mpt[ie] = mpt[ie]*nfelec/nelec
#            mpt[ie] = mpt[ie]*nelect/nelec

        for ie in range(istart, ifermi):
            ave = ave + ft[ie]
#            ave_mpt = ave_mpt + mpt[ie]
        ave = ave/(ifermi-istart)
#        ave_mpt = ave_mpt/(ifermi-istart)

        Chi2lave = 0.

        for i in range(istart, ifermi):
            Chi2minleft = Chi2minleft + (ft[i] - mpt[i])**2
            Chi2lave = Chi2lave + (ave - mpt[i])**2

        Chi2minleft = Chi2minleft/Chi2lave
        Chi2minright = Chi2minleft

        for ie in range(ishiftmax):

            Chi2l = 0.
            Chi2lave = 0.
            Chi2r = 0.
            Chi2rave = 0.

            for i in range(istart, ifermi):

                if i+ie <= iend:
                    Chi2l = Chi2l + (ft[i] - mpt[i+ie])**2
                    Chi2lave = Chi2lave + (ave - mpt[i+ie])**2
                else:
                    Chi2l = Chi2l + ft[i]**2
                    Chi2lave = Chi2lave + ave**2
                if i-ie > 0:
                    Chi2r = Chi2r + (ft[i] - mpt[i-ie])**2
                    Chi2rave = Chi2rave + (ave - mpt[i-ie])**2
                else:
                    Chi2r = Chi2r + ft[i]**2
                    Chi2rave = Chi2rave + ave**2

            Chi2l = Chi2l/Chi2lave
            Chi2r = Chi2r/Chi2rave

            if (Chi2l < Chi2minleft):
                Chi2minleft = Chi2l
                ishiftleft = ie

            if (Chi2r < Chi2minright):
                Chi2minright = Chi2r
                ishiftright = ie

        mptnew = []

        if Chi2minleft < Chi2minright:

            for i in range(xlen):

                if i < xlen-ishiftleft:
                    mptnew.append(mpt[i+ishiftleft])
                else:
                    mptnew.append(0.)
        else:

            for i in range(xlen):

                if i >= ishiftright:
                    mptnew.append(mpt[i-ishiftright])

                else:
                    mptnew.append(0.)
        return Chi2minleft, Chi2minright, ishiftleft, ishiftright, mptnew

    def clear_graph(self):
        """
        Clears graph canvas
        """
        # clear text
        self.xmu_ent.delete(0, Tk.END)

        # clear graph
        self.plt.clear()  # attributes from 'FigureCanvasTkAgg'
        self.canvas.draw()  # attributes from 'FigureCanvasTkAgg'

    def _quit(self):
        """
        Exits or destroys GUI window
        """
        # exit
        root.quit()
        root.destroy()

###############################################################################


class Text_Window(Tk.Frame):
    """
    Creates a visual text structure of the basic functions of pymatgen
    """

    def __init__(self, master):
        """
        Initialize constructor method will automatically invoked the GUI frames including buttons, menubar, labels and canvas

        Args:
            master:
                In Tkinter, master is a toplevel window manager and contains a given widgets
        """

        master.title('Graphical User Interface for Pymatgen')

        Tk.Frame.__init__(self, master, bd=2)

        self.fstruc = ''
        self.source = ''

        # menu bar

        self.menubar = Menu(self)

        menu = Menu(self.menubar, tearoff=0)
        self.menubar.add_cascade(label='File', menu=menu)
        menu.add_command(label='Open', command=self.open_file)
        menu.add_command(label='Save', command=self.save_file)
        menu.add_command(label='Save as', command=self.save_as_file)

        menu = Menu(self.menubar, tearoff=0)
        self.menubar.add_cascade(label='Edit', menu=menu)
        menu.add_command(label='Cut', accelerator='Ctrl+x', command=lambda:
                         self.structure_text.event_generate('<Control-x>'))
        menu.add_command(label='Copy', accelerator='Ctrl+c', command=lambda:
                         self.structure_text.event_generate('<Control-c>'))
        menu.add_command(label='Paste', accelerator='Ctrl+v', command=lambda:
                         self.structure_text.event_generate('<Control-v>'))

        menu = Menu(self.menubar, tearoff=0)
        self.menubar.add_cascade(label='Material Genie', menu=menu)

        menu.add_command(label='Analyze VASP output directory tree'
                         , command=self.analyze_vasp)
        menu.add_command(label='Analyze VASP output directory tree \
                        for ion magnetization'
                         , command=self.get_magnetization)
#       menu.add_command(label='Create VASP input files from POSCAR, CSSR, or\
#                         cif file', command=self.make_vasp_input)
        menu.add_command(label='Find Space Group, from POSCAR, CSSR, cif, or vasprun.xml'\
                         , command=self.find_space_group) 

        menu = Menu(self.menubar, tearoff=0)
        self.menubar.add_cascade(label='Help', menu=menu)

        menu.add_command(label='How to use GUI', command=self.help)
        menu.add_command(label='About', command=self.about)

        try:
            self.master.config(menu=self.menubar)
        except AttributeError:
            self.master.tk.call(master, 'config', '-menu', self.menubar)

        frame2 = Frame(root)
        frame2.pack(anchor=NW)

        b6 = Button(frame2, text='Find Material', command=self.find_material_button)
        b6.grid(row=0, column=0, sticky=Tk.W)

        self.mat_ent = Tk.Entry(frame2)
        self.mat_ent.bind('<Return>', self.find_material)
        self.mat_ent.grid(row=0, column=1, sticky=Tk.W)

        Tk.Label(frame2, text='Enter formula or element list, \n Ex: FE203\
                 or Fe-0') .grid(row=0, column=2, columnspan=2, sticky=Tk.W)

        b6 = Button(frame2, text='Get Structure', command=self.get_structure_button)
        b6.grid(row=1, column=0, sticky=Tk.W)

        self.get_ent = Tk.Entry(frame2)
        self.get_ent.bind('<Return>', self.get_structure)
        self.get_ent.grid(row=1, column=1, sticky=Tk.W)

        Tk.Label(frame2, text='Enter \'Material ID\' to get structure')\
            .grid(row=1, column=2, columnspan=2, sticky=Tk.W)

        # create instruction label
        frame1 = Frame(root)
        frame1.pack(anchor=NW)

        Tk.Label(frame1, text='Browse to select cif, poscar, or vasprun file\
         to load structure') .grid(row=0, column=0, columnspan=2, sticky=Tk.W)

        # create a label and text entry
        Button(frame1, text='Browse', command=self.askopenfile_name)\
            .grid(row=1, column=0, sticky=Tk.W)

        self.cif_ent = Tk.Entry(frame1, width=50)  # frame1 instead of self
        self.cif_ent.grid(row=1, column=1, sticky=Tk.W)

#        create a button

        frame = Frame(root)  # row of buttons
        frame.pack(anchor=NW)  # row of buttoms

        b2 = Button(frame, text='Create a feff.inp file', command=self.msg_box)
        b2.pack(side=LEFT)

        b5 = Button(frame, text='Display Structure', command=self.structure_display)
        b5.pack(side=LEFT)

        b3 = Button(frame, text='Clear text', command=self.clear_text)
        b3.pack(side=LEFT)

        b4 = Button(frame, text='Exit', command=self._quit)
        b4.pack(side=LEFT)

        self.file_opt = option = {}
        option['defaultextension'] = '.cif' or '.xml'
        option['filetypes'] = [('all files', '.*'), ('feff cif files',
                                                     '*.cif'), ('vasprunfiles',
                                                                '*.xml')]
        option['initialdir'] = '../test_files'
        option['initialfile'] = ''
        option['parent'] = root
        option['title'] = 'Select file'

        self.dir_opt = options = {}
        options['initialdir'] = '../test_files'
        options['mustexist'] = False
        option['parent'] = root
        option['title'] = 'Select Directory'

#         create a scroll bar and text box

        self.scroll_bar = Tk.Scrollbar(root)
        self.scroll_bar.pack(side=Tk.RIGHT, fill=Tk.Y)

        self.scroll_xbar = Tk.Scrollbar(root, orient=Tk.HORIZONTAL)
        self.scroll_xbar.pack(side=Tk.BOTTOM, fill=Tk.X)

        self.structure_text = Tk.Text(root)
        self.structure_text.pack(side=Tk.LEFT, fill=Tk.BOTH, expand=1)

    def print_text(self, stuff):

        self.clear_text()
        self.structure_text.insert(Tk.END, stuff)

    def struc(self):
        """
        returns currently loaded structure
        """
        return self.fstruc

    def mpID(self):
        """
        returns currently loaded mp ID number
        """
        return str(self.source)

    def askopenfile_name(self):
        """Returns an opened file in read mode.
        This time the dialog just returns a filename and the file is opened by your own code.
        """

        self.clear_text()

#        get filename
        file_name = tkFileDialog.askopenfilename(**self.file_opt)
        self.source = file_name
        if file_name == '' or file_name == ():
            return
        self.cif_ent.insert(0, file_name)
        file_type = file_name.split(".")[-1]

        if file_type == 'cif':
            r = CifParser(self.source)
            self.fstruc = r.get_structures()[0]

        else:

            self.fstruc = Structure.from_file(file_name)

    def msg_box(self):
        """
        A message box for entering a symbol of absorbing atoms from create\
             a feff.inp file
        """
        self.box = Toplevel()
        label0 = Label(self.box, text='Enter Symbol of absorbing Atom')
        label0.pack()

        self.box.entry0 = Entry(self.box)
        self.box.entry0.pack()

        var = IntVar()
        r1 = Radiobutton(self.box, text='XANES', variable=var, value=1)\
            .pack(anchor=W)
        r2 = Radiobutton(self.box, text='EXAFS', variable=var, value=2)\
            .pack(anchor=W)

        button1 = Button(self.box, text='Submit', command=lambda:
                         self.submit_feff(var, self.box))
        button1.pack()

        button2 = Button(self.box, text='Cancel', command=lambda:
                         self.box.destroy())
        button2.pack()

    def submit_feff(self, var, box):
        """
        Enter symbol of absorbing atoms to convert to feff.inp file

        Args:
            var:
                XANES or EXAFS option
            box:
                is the toplevel manager of the message box window
        """
#        x = FeffinputSet("MaterialsProject")
        self.central_atom = box.entry0.get()

        is_central_atom = False
        for site in self.fstruc:
            if self.central_atom == site.specie.symbol:
                is_central_atom = True

        if is_central_atom:
            print 'var = ', var
            if var.get() == 1:
                self.calc_type = 'XANES'
            else:
                self.calc_type = 'EXAFS'

            if self.fstruc != '':
                structure = self.fstruc
#                feff_dict = FeffInputSet.as_dict(x, structure,
#                                                 self.calc_type, self.source,
#                                                 self.central_atom,)
#                self.feff_input = feff_dict['feff.inp']

                in_dict = MPXANESSet(self.central_atom, structure).all_input()
                h = in_dict["HEADER"]
                pa = in_dict['PARAMETERS']
                po = in_dict['POTENTIALS']
                a = in_dict['ATOMS']
                self.feff_input = str(h) + '\n\n' + str(pa) + '\n\n' + str(po) \
                    + '\n\n' + str(a)
        # display
#                self.structure_text.insert(Tk.END, '\n')
                self.clear_text()
                for line in self.feff_input:
                    self.structure_text.insert(END, line)
            else:
                self.structure_text.insert(1.0, '\nMust Generate a structure\
                 object from either cif_file or vasprun.xml file first')
        else:
            self.structure_text.insert(1.0, '\nCentral Atom Not Found in\
             Structure, Choose Another')

        self.box.destroy()

    def find_material(self, event):
        """
        List materials from MP database using formula or elements
        """
        matproj = mp.MPRester("DIiNE4zmm8ATO0so")
        text = self.mat_ent.get()
        if text == '':
            self.structure_text.insert(1.0, '\nMust Enter Formula like Fe2O3\
             or Elements like Fe-O\n')
        else:
            entries = matproj.get_entries(text)
            for item in entries:
                text = '\nMaterial ID:'+str(item.data['material_id'])+'  Formula: '+item.data['pretty_formula']
                text = text+'  Crystal System:  '+item.data['spacegroup']['crystal_system']
                text = text+'\n          Symmetry Number:'+str(item.data['spacegroup']['number'])
                text = text+'  Energy per Atom:'+str(item.data['energy_per_atom'])+'\n\n'
                self.structure_text.insert(1.0, text)
                self.structure_text.config(yscrollcommand=self.scroll_bar.set)
                self.scroll_bar.config(command=self.structure_text.yview)

    def find_material_button(self):
        """
        List materials from MP database using formula or elements
        """
        matproj = mp.MPRester("DIiNE4zmm8ATO0so")
        text = self.mat_ent.get()
        if text == '':
            self.structure_text.insert(1.0, '\nMust Enter Formula like Fe2O3 or Elements like Fe-O\n')
        else:
            entries = matproj.get_entries\
                        (text, inc_structure="final", property_data=
                         ["material_id",
                          "pretty_formula",
                          "spacegroup",
                          "energy_per_atom"])
            if len(entries) > 0:
                print entries[0]

                for item in entries:
                    text = '\nMaterial ID:'+str(item.data['material_id']) + '  Formula: ' + item.data['pretty_formula']
                    text = text+'  Crystal System:  ' + item.data['spacegroup']['crystal_system']
                    text = text+'\n          Symmetry Number:' + str(item.data['spacegroup']['number'])
                    text = text+'  Energy per Atom:' + str(item.data['energy_per_atom']) + '\n\n'
                    self.structure_text.insert(1.0, text)
                    self.structure_text.config(yscrollcommand=self.scroll_bar.set)
                    self.scroll_bar.config(command=self.structure_text.yview)
            else:
                print "matproj returned no entries"

    def get_structure(self, event):
        """
        Gets material structure object using material ID from MP database
        """
        matproj = mp.MPRester("DIiNE4zmm8ATO0so")
        ID = self.get_ent.get()
        self.source = ID
        if ID == '':
            self.structure_text.insert(1.0, '\nNo Structure ID Number Entered\n')
        else:
            self.fstruc = matproj.get_structure_by_material_id(str(ID))
            self.structure_text.insert(1.0, self.fstruc)
            self.structure_text.config(yscrollcommand=self.scroll_bar.set)
            self.scroll_bar.config(command=self.structure_text.yview)
            self.structure_text.insert(1.0, '\n\n')

    def get_structure_button(self):
        """
        Gets material structure object using material ID from MP database
        """
        matproj = mp.MPRester("DIiNE4zmm8ATO0so")
        ID = self.get_ent.get()
        self.source = ID
        if ID == '':
            self.structure_text.insert(1.0, '\nNo Structure ID Number Entered\n')
        else:
            self.fstruc = matproj.get_structure_by_material_id(str(ID))
            nelect = matproj.query(ID, ["input.parameters.NELECT"])
            self.structure_text.insert(1.0, self.fstruc)
            self.structure_text.insert(1.0, str(nelect)+"\n\n")
            self.structure_text.config(yscrollcommand=self.scroll_bar.set)
            self.scroll_bar.config(command=self.structure_text.yview)
            self.structure_text.insert(1.0, '\n\n')

    def structure_display(self):
        """
        Displays structure summary
        """

        self.structure_text.delete(1.0, Tk.END)

        if self.fstruc != '':
            structure = self.fstruc
            self.structure_text.insert(Tk.END, structure)
#              add scroll bar to text
            self.structure_text.config(yscrollcommand=self.scroll_bar.set)
            self.scroll_bar.config(command=self.structure_text.yview)

        else:

            self.structure_text.insert(Tk.END, 'Must Generate a structure object from cif_file')

    def analyze_vasp(self):
        """
        Extract computed properties from a VASP run tree using vasprun.xml files,
        use Browse button to locate top of VASP tree
        """

        vasp_root_dir = tkFileDialog.askdirectory()
        if vasp_root_dir == '' or vasp_root_dir == ():
            self.structure_text.insert(1.0, '\nSelect Directory')
        else:
            self.structure_text.insert(1.0, '\nRoot Directory\n' + vasp_root_dir + '\n')

            execute = 'python ' + pmg_dir + ' analyze '+vasp_root_dir+' -f -v -d -p -s energy_per_atom'
            text_out = subprocess.Popen([execute], shell=True, stdout=subprocess.PIPE).communicate()[0]            
            self.structure_text.insert(1.0, text_out+'\n')

            self.structure_text.config(yscrollcommand=self.scroll_bar.set)
            self.scroll_bar.config(command=self.structure_text.yview)
            self.structure_text.config(wrap=Tk.NONE, xscrollcommand=self.scroll_xbar.set)
            self.scroll_xbar.config(command=self.structure_text.xview)

    def get_magnetization(self):
        """
        Extract computed properties for ion magnetization from a VASP run tree using vasprun.xml files,
        use Browse button to locate top of VASP tree
        """

        vasp_root_dir = tkFileDialog.askdirectory()
        if vasp_root_dir == '' or vasp_root_dir == ():
            self.structure_text.insert(1.0, '\nSelect Directory')
        else:
            self.structure_text.insert(1.0, '\nRoot Directory\n' + vasp_root_dir + '\n')
            execute = 'python ' + pmg_dir + ' analyze ' + vasp_root_dir + ' -m 0-6'
            text_out = subprocess.Popen([execute], shell=True, stdout=subprocess.PIPE).communicate()[0]            
            self.structure_text.insert(1.0, text_out+'\n')

            self.structure_text.config(yscrollcommand=self.scroll_bar.set)
            self.scroll_bar.config(command=self.structure_text.yview)
            self.structure_text.config(wrap=Tk.NONE, xscrollcommand=self.scroll_xbar.set)
            self.scroll_xbar.config(command=self.structure_text.xview)

#    def make_vasp_input(self):
#        """generate a set of VASP input files"""
#        file_name=tkFileDialog.askopenfilename(**self.file_opt)
#        if file_name == '' or file_name==():
#            return
#        self.cif_ent.delete(0, END)
#        self.cif_ent.insert(0, file_name)

#        execute='python pmg.py convert ' + file_name +' VASP_Input -o VASP'
#        subprocess.Popen([execute], shell=True)
#        self.structure_text.insert(END, 'VASP input has generated in ')

    def find_space_group(self):
        """
        Find space group symmetry
        """
        file_name = tkFileDialog.askopenfilename(**self.file_opt)
        if file_name == '' or file_name == ():
            return
        self.cif_ent.delete(0, END)
        self.cif_ent.insert(0, '\n'+file_name)

        execute = 'python ' + pmg_dir + '/pmg.py structure -f ' + file_name + ' -s .1'
        text_out = subprocess.Popen([execute], shell=True, stdout=subprocess.PIPE).communicate()[0]
        self.structure_text.insert(END, text_out+'\n')

    def help(self):
        """
        the help tab gives you a brief description on each functions on the GUI
        """

        description = "A graphical user interface that supports the basic functions of pymatgen, including.. \n \n \
        Menubar:\n \
            File:\n \
                open \n \
                save\n \
                save as \n \
            Edit:\n \
                cut \n \
                copy \n \
                paste \n \
            Material Genie: \n \
                Analyze VASP output directory tree- Extract computed properties from a VASP run tree using vasprun.xml files \n \
                Analyze VASP output directory tree for ion magnetization- Extract computed properties for ion magnetization from a VASP run tree using vasprun.xml files\n \
                Find Space Group, from POSCAR, CSSR, cif, or vasprun.xml- Find space group symmetry\n\n \
        buttons: \n \
            Plot: \n \
                Plot XMU.dat- Plot feff cross section \n \
                Plot LDOS from FEFF LDOS00.dat file:\n \
                    Site- Plot feff LDOS density of states by site\n \
                    Element- Plot feff LDOS density of states by element\n \
                    Orbital- Plot feff LDOS density of states by orbital\n \
                Plot DOS from vasprun.xml file:\n \
                    Site- Plot feff DOS density of states by site\n \
                    Element- Plot feff DOS density of states by element\n \
                    Orbital- Plot feff DOS density of states by orbital\n \
                Plot Charge integration-  Plot charge integration\n \
            View structure- visualization of selected structure\n \
            Clear graph- clear graph\n \
            Exit- destroy GUI window\n\n \
            Find Materials- List materials from MP database using formula or elements\n \
            Get Structure- Gets material structure object using material ID from MP database\n \
            Browse- From file dialog opens a filename\n \
            Create a feff.inp file:\n \
                message box: Enter symbol of absorbing atoms\n \
                    Radio button- XANES or EXAFS\n \
                    Submit- converts structure to feff.inp file\n \
                    Cancel- destroys message box\n \
            Display Structure- Displays structure summary\n \
            Clear text- Clear text\n \
            Exit- destroy GUI window"

        self.structure_text.insert(1.0, description)
#        add scroll bar to text
        self.structure_text.config(yscrollcommand=self.scroll_bar.set)
        self.scroll_bar.config(command=self.structure_text.yview)
        self.structure_text.config(wrap=Tk.NONE, xscrollcommand=self.scroll_xbar.set)
        self.scroll_xbar.config(command=self.structure_text.xview)

    def about(self):
        """
        About tab gives detail about GUI.
        """

        detail = "A Graphical user interface that supports the basic functions of pymatgen.\n \n\
        \nAuthors: Megan LaRue \n\
    \nCredits: Alan Dozier, Shyue Ping Ong, Anubhav Jain \n\
        \nReference: \nShyue Ping Ong, William Davidson Richards, Anubhav Jain, Geoffroy Hautier,\
        \nMichael Kocher, Shreyas Cholia, Dan Gunter, Vincent Chevrier, Kristin A. Persson,\
        \nGerbrand Ceder. Python Materials Genomics (pymatgen) : A Robust,\
        \nOpen-Source Python Library for Materials Analysis.\
        \nComputational Materials Science, 2013, 68, 314319. doi:10.1016/j.commatsci.2012.10.028 \n\
        \nCopyright: Copyright 2011, The Materials Project \n\
        \nVersion: 1.2 \n\
        \nMaintainer: Megan LaRue \n\
        \nEmail: meganlarue79@gmail.com \n\
        \nStatus: Beta \n\
        \nDate: August 12, 2013 \n"

        self.structure_text.insert(1.0, detail)
#        add scroll bar to text
        self.structure_text.config(yscrollcommand=self.scroll_bar.set)
        self.scroll_bar.config(command=self.structure_text.yview)
        self.structure_text.config(wrap=Tk.NONE, xscrollcommand=self.scroll_xbar.set)
        self.scroll_xbar.config(command=self.structure_text.xview)

    def clear_text(self):
        """
        Clears canvas text
        """
        self.structure_text.delete(1.0, Tk.END)

    def open_file(self):
        """
        General file opening to display in text box
        """
        file_name = tkFileDialog.askopenfilename()

        self.sfname = file_name

        with open(file_name, 'r') as f:
            text_data = f.read()
        f.closed
        self.clear_text()
        self.structure_text.insert(END, text_data)
        self.structure_text.config(yscrollcommand=self.scroll_bar.set)
        self.scroll_bar.config(command=self.structure_text.yview)

    def save_as_file(self):
        """
        Names & saves file from the text canvas
        """

        text_data = self.structure_text.get(0.0, END)
        file_name = tkFileDialog.asksaveasfilename()
        f = open(file_name, 'w')
        f.write(text_data)
        f.close()

    def save_file(self):
        """
        Saves file from the text canvas
        """

        text_data = self.structure_text.get(0.0, END)

        if (text_data != '') and (self.sfname != ''):
            f = open(self.sfname, 'w')
            f.write(text_data)
            f.close()

    def _quit(self):
        """
        Exits or destroys GUI window
        """
        root.quit()
        root.destroy()


class DosPlotter(object):

    __author__ = "Shyue Ping Ong, Geoffroy Hautier"
    __copyright__ = "Copyright 2012, The Materials Project"
    __version__ = "0.1"
    __maintainer__ = "Shyue Ping Ong"
    __email__ = "shyuep@gmail.com"
    __date__ = "May 1, 2012"

    """
    Class for plotting DOSs. Note that the interface is extremely flexible
    given that there are many different ways in which people want to view
    DOS. The typical usage is::

        # Initializes plotter with some optional args. Defaults are usually
        # fine,
        plotter = DosPlotter()

        # Adds a DOS with a label.
        plotter.add_dos("Total DOS", dos)

        # Alternatively, you can add a dict of DOSs. This is the typical
        # form returned by CompleteDos.get_spd/element/others_dos().
        plotter.add_dos_dict({"dos1": dos1, "dos2": dos2})
        plotter.add_dos_dict(complete_dos.get_spd_dos())

    Args:
        plt: self.plt defined as f.add_subplot(111) so plot appears in GUI window
        zero_at_efermi: Whether to shift all Dos to have zero energy at the
            fermi energy. Defaults to True.
        stack: Whether to plot the DOS as a stacked area graph
        key_sort_func: function used to sort the dos_dict keys.
        sigma: A float specifying a standard deviation for Gaussian smearing
            the DOS for nicer looking plots. Defaults to None for no
            smearing.
    """

    def __init__(self, plt, zero_at_efermi=True, stack=False, sigma=None):
        from matplotlib.font_manager import FontProperties
        self.fontp = FontProperties()
        self.plt = plt
        self.zero_at_efermi = zero_at_efermi
        self.stack = stack
        self.sigma = sigma
        self._doses = OrderedDict()
        self.ylimit = None

    @property
    def ylim(self):
        return self.ylimit

    def add_dos(self, label, dos):
        """
        Adds a dos for plotting.

        Args:
            label:
                label for the DOS. Must be unique.
            dos:
                Dos object
        """
        energies = dos.energies - dos.efermi if self.zero_at_efermi \
            else dos.energies
        densities = dos.get_smeared_densities(self.sigma) if self.sigma \
            else dos.densities
        efermi = dos.efermi
        self._doses[label] = {'energies': energies, 'densities': densities,
                              'efermi': efermi}

    def add_dos_dict(self, dos_dict, key_sort_func=None):
        """
        Add a dictionary of doses, with an optional sorting function for the
        keys.

        Args:
            dos_dict: dict of {label: Dos}
            key_sort_func: function used to sort the dos_dict keys.
        """
        if key_sort_func:
            keys = sorted(dos_dict.keys(), key=key_sort_func)
        else:
            keys = dos_dict.keys()
        for label in keys:
            self.add_dos(label, dos_dict[label])

    def get_dos_dict(self):
        """
        Returns the added doses as a json-serializable dict. Note that if you
        have specified smearing for the DOS plot, the densities returned will
        be the smeared densities, not the original densities.

        Returns:
            Dict of dos data. Generally of the form, {label: {'energies':..,
            'densities': {'up':...}, 'efermi':efermi}}
        """
        return jsanitize(self._doses)

    def get_plot(self, xlim=None, ylim=None, scale=False, ccolor=False):
        """
        Get a matplotlib plot showing the DOS.

        Args:
            xlim: Specifies the x-axis limits. Set to None for automatic
                determination.
            ylim: Specifies the y-axis limits.
        """
        from pymatgen.util.plotting_utils import get_publication_quality_plot
        color_order = ['r', 'b', 'g', 'c', 'm', 'k']

        y = None
        alldensities = []
        allenergies = []
        # Note that this complicated processing of energies is to allow for
        # stacked plots in matplotlib.
        for key, dos in self._doses.items():
            energies = dos['energies']
            densities = dos['densities']
            if not y:
                y = {Spin.up: np.zeros(energies.shape),
                     Spin.down: np.zeros(energies.shape)}
            newdens = {}
            for spin in [Spin.up, Spin.down]:
                if spin in densities:
                    if self.stack:
                        y[spin] += densities[spin]
                        newdens[spin] = y[spin].copy()
                    else:
                        newdens[spin] = densities[spin]
            allenergies.append(energies)
            alldensities.append(newdens)

        keys = list(self._doses.keys())
        keys.reverse()
        alldensities.reverse()
        allenergies.reverse()
        allpts = []
        for i, key in enumerate(keys):
            x = []
            y = []
            for spin in [Spin.up, Spin.down]:
                if spin in alldensities[i]:
                    densities = list(int(spin) * alldensities[i][spin])
                    energies = list(allenergies[i])
                    if spin == Spin.down:
                        energies.reverse()
                        densities.reverse()
                    x.extend(energies)
                    y.extend(densities)
            allpts.extend(zip(x, y))
            if scale:
                ymax = max(y)
                if ymax > 0.:
                    s = ylim[1]/ymax
                y[:] = [x1*s for x1 in y]
            if ccolor:
                icolor = i+1
            else:
                icolor = i
            if self.stack:
                self.plt.fill(x, y, color=color_order
                              [icolor % len(color_order)], label=str(key))
            else:
                self.plt.plot(x, y, color=color_order
                              [icolor % len(color_order)], label=str(key))
            if not self.zero_at_efermi:
                ylim = self.plt.get_ylim()
                self.plt.plot([self._doses[key]['efermi'],
                               self._doses[key]['efermi']], ylim,
                              color_order[i % 4] + '--', linewidth=2)

        self.plt.set_xlabel('Energies (eV)')
        self.plt.set_ylabel('Density of states')
        if xlim:
            self.plt.set_xlim(xlim)
        if ylim:
            self.plt.set_ylim(ylim)
        else:
            xlim = self.plt.get_xlim()
            relevanty = [p[1] for p in allpts
                         if xlim[0] < p[0] < xlim[1]]
            self.plt.set_ylim((min(relevanty), max(relevanty)))
            self.ylimit = self.plt.get_ylim()

        if self.zero_at_efermi:
            ylim = self.plt.get_ylim()
            self.plt.plot([0, 0], ylim, 'k--', linewidth=2)

        self.fontp.set_size('x-small')
        self.plt.legend(prop=self.fontp, loc=0)

        return self.plt

    def save_plot(self, filename, img_format="eps", xlim=None, ylim=None):
        """
        Save matplotlib plot to a file.

        Args:
            filename: Filename to write to.
            img_format: Image format to use. Defaults to EPS.
            xlim: Specifies the x-axis limits. Set to None for automatic
                determination.
            ylim: Specifies the y-axis limits.
        """
        self.plt = self.get_plot(xlim, ylim)
        self.plt.savefig(filename, format=img_format)

    def show(self, xlim=None, ylim=None):
        """
        Show the plot using matplotlib.

        Args:
            xlim: Specifies the x-axis limits. Set to None for automatic
                determination.
            ylim: Specifies the y-axis limits.
        """
        self.self.plt = self.get_plot(xlim, ylim)
        self.self.plt.show()

#        runs GUI and creates instances of classes

gra = Graph_Window(root)

cif = Text_Window(root)


Tk.mainloop()
